module

public import Compose.Ui.Draw.Gpu.Encode
public meta import Compose.Ui.Draw.Gpu.Encode
public import Compose.Ui.Draw.Gpu.Shaders
public meta import Compose.Ui.Draw.Gpu.Shaders
public import Compose.Ui.Draw.Gpu.TextEngine
public meta import Compose.Ui.Draw.Gpu.TextEngine

public section

/-!
# GPU frame renderer (`Compose/Ui/Draw/Gpu/Renderer.lean`)

Per-window GPU state and the frame lifecycle: resolve text + images (IO —
uncached bitmaps upload into a process-wide texture cache) → encode
(pure) → acquire the frame's pooled textures (layers, and — when the frame
has backdrop panels — the full-screen snapshot plus two downsample textures
per panel) + grow GPU buffers (2×, never shrink) → one transfer-buffer
write + copy pass (`cycle := true` throughout — probe-verified to preserve
in-flight data) → acquire the swapchain texture (blocking or not per
`mayBlock`; `none` still submits the copy work and reports a skipped
frame) → one render pass per offscreen layer (innermost-first, cleared
transparent; blurred layers append two separable Gaussian passes bouncing
through a second pooled texture) → then the target work: without backdrops,
one clear-and-replay pass; with them, the **progressive snapshot** — the
target list replays into a full-screen snapshot texture segment by segment:
the prefix behind the first panel, then per backdrop its region is
downsampled (once, twice past σ 32) and separably blurred off the snapshot
*as painted so far*, and a reopened (`loadOp .load`) snapshot pass
composites the frosted panel quad (through the refracting glass pipeline
when the panel's `Refraction` is on) and continues to the next panel — so
each panel frosts everything beneath it, earlier panels' frost included;
the target pass then clears and blits the finished snapshot 1:1 nearest →
submit (present is implicit).

Layer textures come from a per-window pool: dimensions quantized up to 64 px,
best-fit ≥ the request, entries released after sitting idle for
`poolTrimAge` frames — steady-state animation reuses the same textures with
`cycle := true` semantics from the render-pass clear.

One `Gpu.Device` is shared per process (lazily created, claiming every GPU
window); pipelines and the sampler live in this structure so they stay
reachable while bound (SDL binds do not retain them).
-/

namespace Compose.Draw.Gpu
open Sdl.Gpu

/-- The process-wide GPU device (SDL_GPU supports one device claiming many
windows; MSL or SPIR-V shader format, debug mode via `COMPOSE_GPU_DEBUG`). -/
private initialize deviceRef : IO.Ref (Option Device) ← IO.mkRef none

/-- The last prepared frame's batch statistics — the GPU analog of the debug
`tessellationCount` counter (shared across windows, like it). -/
initialize frameStats : IO.Ref FrameStats ← IO.mkRef {}

/-- Whether `COMPOSE_GPU_DEBUG` is set: debug-mode device creation, and the
encode/resolve walk-drift tripwire throws instead of warning. -/
private initialize gpuDebug : Bool ← return (← IO.getEnv "COMPOSE_GPU_DEBUG").isSome

/-- The shared device, created on first use. Throws where SDL_GPU has no
backend (always under the dummy video driver — the GPU backend is real-driver
only). The format mask offers MSL and SPIR-V — Metal picks MSL, Vulkan picks
SPIR-V (`Pipelines.create` selects the matching shader sources).
`COMPOSE_GPU_DRIVER` forces a specific SDL_GPU driver (e.g. `vulkan` on macOS
runs the SPIR-V pipelines over MoltenVK — the desktop validation path for the
Android port). -/
def getDevice : IO Device := do
  if let some d := ← deviceRef.get then
    return d
  let driver ← IO.getEnv "COMPOSE_GPU_DRIVER"
  let d ← createDevice (ShaderFormat.msl ||| .spirv) (debugMode := gpuDebug) (name := driver)
  d.setAllowedFramesInFlight 2
  deviceRef.set (some d)
  return d

/-- Process-wide image texture cache: `ImageBitmap.id` → its premultiplied
GPU texture (one shared device, so textures work across windows). Never
evicted in steady state — images are immutable and id-keyed; textures live
until process exit or a `dropImageTexCache` (backend `invalidateCaches`). -/
private initialize imageTexCache : IO.Ref (Array (Nat × Texture)) ← IO.mkRef #[]

/-- Release every cached image texture and forget the cache — the process-
wide half of the GPU backend's `invalidateCaches` (`lowMemory` and the
renderer-reset events). Textures re-upload lazily on the next frame that
draws the image; SDL defers destruction of textures still referenced by
in-flight frames. -/
def dropImageTexCache : IO Unit := do
  for (_, tex) in (← imageTexCache.get) do
    tex.release
  imageTexCache.set #[]

/-- Upload one bitmap as a premultiplied `r8g8b8a8Unorm` texture: staging
bytes from `ImageBitmap.premultipliedBytes`, one copy pass on `cb` (before
the frame's render passes), transfer buffer released immediately. -/
private def uploadImage (dev : Device) (cb : CommandBuffer)
    (img : Compose.Draw.ImageBitmap) : IO Texture := do
  let w := UInt32.ofNat (max 1 img.width)
  let h := UInt32.ofNat (max 1 img.height)
  let tex ← dev.createTexture
    { format := .r8g8b8a8Unorm, usage := .sampler, width := w, height := h }
  let bytes ← img.premultipliedBytes
  if !bytes.isEmpty then
    let tb ← dev.createTransferBuffer .upload (UInt32.ofNat bytes.size)
    tb.write bytes (cycle := false)
    let cp ← cb.beginCopyPass
    cp.uploadToTexture { buffer := tb }
      { texture := tex, w := UInt32.ofNat img.width, h := UInt32.ofNat img.height }
      (cycle := false)
    cp.finish
    tb.release
  return tex

private partial def collectImages (dev : Device) (cb : CommandBuffer)
    (idxs : IO.Ref (Array Nat)) (table : IO.Ref (Array (Nat × Texture))) :
    Prim → IO Unit
  | .image _ img _ _ _ => do
    -- Already in this frame's table?
    let mut found : Option Nat := none
    let mut j := 0
    for (id, _) in (← table.get) do
      if found.isNone && id == img.id then
        found := some j
      j := j + 1
    match found with
    | some i => idxs.modify (·.push i)
    | none =>
      -- Process cache, uploading on miss.
      let tex ← do
        let mut hit : Option Texture := none
        for (id, t) in (← imageTexCache.get) do
          if hit.isNone && id == img.id then
            hit := some t
        match hit with
        | some t => pure t
        | none =>
          let t ← uploadImage dev cb img
          imageTexCache.modify (·.push (img.id, t))
          pure t
      let i := (← table.get).size
      table.modify (·.push (img.id, tex))
      idxs.modify (·.push i)
  | .layer _ _ _ content => do
    for p in content do
      collectImages dev cb idxs table p
  | _ => pure ()

/-- Resolve every image primitive in `list` (walk order = encode order): the
per-primitive index into the returned frame texture table, uploading uncached
bitmaps into the process-wide cache via copy passes on `cb`. -/
def resolveImages (dev : Device) (cb : CommandBuffer) (list : DisplayList) :
    IO (Array Nat × Array Texture) := do
  let idxs ← IO.mkRef (#[] : Array Nat)
  let table ← IO.mkRef (#[] : Array (Nat × Texture))
  for p in list do
    collectImages dev cb idxs table p
  return (← idxs.get, (← table.get).map (·.2))

/-- One GPU buffer with its current byte capacity. -/
private structure Slot where
  buffer : Buffer
  capacity : Nat

/-- Per-window frame buffers, grown geometrically and never shrunk. -/
private structure FrameBuffers where
  quad : Option Slot := none
  shadow : Option Slot := none
  meshV : Option Slot := none
  meshI : Option Slot := none
  glyphV : Option Slot := none
  glyphI : Option Slot := none
  layerV : Option Slot := none
  layerI : Option Slot := none
  imageV : Option Slot := none
  imageI : Option Slot := none
  transfer : Option TransferBuffer := none

/-- One pooled offscreen layer texture (64 px-quantized dimensions). -/
private structure PoolEntry where
  tex : Texture
  w : UInt32
  h : UInt32
  /-- Frames since last use (released past `poolTrimAge`). -/
  idle : Nat := 0
  /-- Claimed by the frame being prepared. -/
  used : Bool := false

/-- Frames a pooled layer texture may sit idle before release. -/
private def poolTrimAge : Nat := 120

/-- The pooled textures backing one encoded layer: the content texture the
composite samples (with its pool dimensions — best-fit, so ≥ the request),
and, for blurred layers (`LayerEnc.sigma > 0`), a second pooled ping texture
the separable passes bounce through (content → ping → content). -/
private structure LayerTex where
  tex : Texture
  w : UInt32
  h : UInt32
  blurTex : Option Texture := none
  blurW : UInt32 := 0
  blurH : UInt32 := 0

/-- The two pooled textures one backdrop panel's downsample/blur chain
bounces through, both sized for the region's first halving. The chain ends
where it started an H/V round-trip: level 1 ends in `a`, level 2 in `b`
(`BackdropTex.final`). -/
private structure BackdropTex where
  a : Texture
  aw : UInt32
  ah : UInt32
  b : Texture
  bw : UInt32
  bh : UInt32

/-- The texture the composite samples: where the copy chain ended (odd
halvings → `a`, even → `b`) — the H/V blur round-trip returns there. -/
private def BackdropTex.final (bt : BackdropTex) (levels : Nat) :
    Texture × UInt32 × UInt32 :=
  if levels % 2 == 1 then (bt.a, bt.aw, bt.ah) else (bt.b, bt.bw, bt.bh)

/-- Every pooled texture backing one frame: per-layer content (+ blur ping)
textures, the full-screen snapshot (only when the frame splits at a
backdrop), and each backdrop panel's downsample pair. -/
private structure FrameTextures where
  layers : Array LayerTex := #[]
  snapshot : Option (Texture × UInt32 × UInt32) := none
  backdrops : Array BackdropTex := #[]

/-- Per-window GPU renderer state. -/
structure GpuRenderer where
  /-- The shared device. -/
  dev : Device
  /-- The claimed window. -/
  window : Sdl.Window
  /-- Pipelines against the window's swapchain format (kept reachable —
  binds do not retain). -/
  pipelines : Pipelines
  /-- Glyph-atlas / layer sampler (nearest — both are drawn 1:1
  pixel-snapped). -/
  sampler : Sampler
  /-- Linear/clamp-to-edge sampler (scaled image draws; transformed layers
  and blur reuse it in later waves). -/
  samplerLinear : Sampler
  /-- Frame buffers (mutable: grown across frames). -/
  private buffers : IO.Ref FrameBuffers
  /-- Offscreen layer texture pool. -/
  private pool : IO.Ref (Array PoolEntry)

/-- Create the per-window renderer state for an already-claimed window. -/
def GpuRenderer.create (dev : Device) (window : Sdl.Window) : IO GpuRenderer := do
  let fmt ← dev.getSwapchainTextureFormat window
  return { dev, window
           pipelines := ← Pipelines.create dev fmt
           sampler := ← dev.createSampler
             { minFilter := .nearest, magFilter := .nearest
               addressModeU := .clampToEdge, addressModeV := .clampToEdge
               addressModeW := .clampToEdge }
           samplerLinear := ← dev.createSampler
             { minFilter := .linear, magFilter := .linear
               addressModeU := .clampToEdge, addressModeV := .clampToEdge
               addressModeW := .clampToEdge }
           buffers := ← IO.mkRef {}
           pool := ← IO.mkRef #[] }

/-- Round `n` up to a 16-byte boundary (transfer-region alignment). -/
private def align16 (n : Nat) : Nat := (n + 15) / 16 * 16

/-- Ensure a GPU buffer of at least `needed` bytes (grow to the next power of
two, min 4 KiB; the old buffer is released — SDL defers destruction while
in-flight frames reference it). Untouched when `needed` is 0. -/
private def ensureSlot (dev : Device) (cur : Option Slot) (usage : BufferUsageFlags)
    (needed : Nat) : IO (Option Slot) := do
  if needed == 0 then
    return cur
  if let some s := cur then
    if s.capacity ≥ needed then
      return cur
    s.buffer.release
  let capacity := max 4096 needed.nextPowerOfTwo
  return some { buffer := ← dev.createBuffer usage (UInt32.ofNat capacity), capacity }

/-- Upload one staging region into its GPU buffer (no-op when empty). -/
private def uploadRegion (cp : CopyPass) (tb : TransferBuffer) (offset : Nat)
    (bytes : ByteArray) (slot : Option Slot) : IO Unit := do
  if bytes.isEmpty then return
  let some s := slot | return
  cp.uploadToBuffer { buffer := tb, offset := UInt32.ofNat offset }
    { buffer := s.buffer, size := UInt32.ofNat bytes.size } (cycle := true)

/-- Quantize a (whole-px, positive) layer extent up to a multiple of 64. -/
private def quantize64 (x : Float32) : UInt32 :=
  let n := max 1 x.toUInt32
  (n + 63) / 64 * 64

/-- Best-fit chooser over `(w, h, used)` pool shapes: the smallest-area unused
entry ≥ the request (ties → first). Pure so the policy is `#guard`-testable;
first-fit would let a small layer claim the pooled full-screen texture and
force a fresh full-screen allocation for the next big one. -/
private def bestFitIdx (entries : Array (UInt32 × UInt32 × Bool)) (w h : UInt32) :
    Option Nat := Id.run do
  let mut best : Option (Nat × Nat) := none   -- (index, area)
  for i in [0:entries.size] do
    let (ew, eh, used) := entries[i]!
    if !used && ew ≥ w && eh ≥ h then
      let area := ew.toNat * eh.toNat
      if best.all (area < ·.2) then
        best := some (i, area)
  return best.map (·.1)

-- The small request takes the small entry even when a big one sits first.
#guard bestFitIdx #[(1920, 1088, false), (64, 64, false)] 64 64 == some 1
-- A too-small entry is skipped (both dimensions must fit).
#guard bestFitIdx #[(64, 64, false), (128, 128, false)] 65 64 == some 1
-- Used entries never match; an exhausted pool misses.
#guard bestFitIdx #[(64, 64, true), (128, 128, false)] 64 64 == some 1
#guard bestFitIdx #[(64, 64, true)] 64 64 == none
-- Equal areas tie to the first entry.
#guard bestFitIdx #[(128, 64, false), (64, 128, false)] 64 64 == some 0

/-- Best-fit one unused pooled texture ≥ the quantized request (smallest area
wins; creating on miss), marking it used. Returns the updated pool and the
texture with its (pool) dimensions. -/
private def poolAcquire (dev : Device) (fmt : TextureFormat) (pool : Array PoolEntry)
    (w h : UInt32) : IO (Array PoolEntry × Texture × UInt32 × UInt32) := do
  if let some i := bestFitIdx (pool.map fun e => (e.w, e.h, e.used)) w h then
    if h : i < pool.size then
      let e := pool[i]
      return (pool.modify i ({ · with used := true, idle := 0 }), e.tex, e.w, e.h)
  let tex ← dev.createTexture
    { format := fmt, usage := TextureUsageFlags.sampler ||| .colorTarget
      width := w, height := h }
  return (pool.push { tex, w, h, used := true }, tex, w, h)

/-- Acquire every pooled texture the frame needs — per-layer content (+ ping
for blurred layers), the full-screen snapshot when `snapshotDims` is set
(a frame with backdrop panels), and each backdrop's downsample pair (both at
the region's first halving, `backdropLevelDim`) — then age and trim the
pool: entries idle past `poolTrimAge` frames are released. -/
private def acquireFrameTextures (r : GpuRenderer) (fmt : TextureFormat)
    (layers : Array LayerEnc) (snapshotDims : Option (UInt32 × UInt32))
    (backdrops : Array BackdropEnc) : IO FrameTextures := do
  let mut pool := (← r.pool.get).map fun e => { e with used := false }
  let mut lts : Array LayerTex := Array.emptyWithCapacity layers.size
  for l in layers do
    let w := quantize64 l.bounds.width
    let h := quantize64 l.bounds.height
    let (pool', tex, tw, th) ← poolAcquire r.dev fmt pool w h
    pool := pool'
    if l.sigma > 0 then
      let (pool'', btex, bw, bh) ← poolAcquire r.dev fmt pool w h
      pool := pool''
      lts := lts.push { tex, w := tw, h := th, blurTex := some btex, blurW := bw, blurH := bh }
    else
      lts := lts.push { tex, w := tw, h := th }
  let mut snapshot : Option (Texture × UInt32 × UInt32) := none
  if let some (tw, th) := snapshotDims then
    let (pool', tex, sw, sh) ← poolAcquire r.dev fmt pool
      (quantize64 (Float32.ofNat tw.toNat)) (quantize64 (Float32.ofNat th.toNat))
    pool := pool'
    snapshot := some (tex, sw, sh)
  let mut bts : Array BackdropTex := Array.emptyWithCapacity backdrops.size
  for b in backdrops do
    let w1 := quantize64 (backdropLevelDim b.region.width 1)
    let h1 := quantize64 (backdropLevelDim b.region.height 1)
    let (pool', ta, aw, ah) ← poolAcquire r.dev fmt pool w1 h1
    let (pool'', tb, bw, bh) ← poolAcquire r.dev fmt pool' w1 h1
    pool := pool''
    bts := bts.push { a := ta, aw, ah, b := tb, bw, bh }
  let mut kept : Array PoolEntry := #[]
  for e in pool do
    if e.used then
      kept := kept.push e
    else if e.idle + 1 ≥ poolTrimAge then
      e.tex.release
    else
      kept := kept.push { e with idle := e.idle + 1 }
  r.pool.set kept
  return { layers := lts, snapshot, backdrops := bts }

/-- The packed composite quads of the frame, at fixed slots so replay draws
by arithmetic offset. Layer `i` owns vertices `4i..4i+3` and indices
`6i..6i+5` (`DrawCmd.layer i`), positioned at the layer bounds' corners
mapped through the composite transform (a transformed layer renders
axis-aligned into its texture; only this quad rotates/scales), with UVs
covering the content's fraction of the pooled texture and the group alpha in
the vertex color.

When the frame splits at a backdrop (`snapshot` set, carrying the target
extent and the snapshot texture's pool dimensions), the build appends — with
`L = layers.size` — the 1:1 snapshot **blit** quad at slot `L`, and per
backdrop `i` three slots: the first **downsample** quad at `L + 1 + 3i`
(the region's fraction of the snapshot → the level-1 extent at the origin),
the second at `L + 2 + 3i` (level 1 → level 2; packed but undrawn for
one-halving panels), and the **panel** composite at `L + 3 + 3i` (the panel
rect, UVs addressing it inside the blurred region at the final level). -/
private def layerComposites (layers : Array LayerEnc)
    (texs : Array LayerTex)
    (snapshot : Option (Float32 × Float32 × UInt32 × UInt32) := none)
    (backdrops : Array BackdropEnc := #[])
    (btexs : Array BackdropTex := #[]) : ByteArray × ByteArray := Id.run do
  let mut verts := ByteArray.empty
  let mut idx := ByteArray.empty
  let mut quads := 0
  -- One quad: corners (x0,y0)-(x1,y1), UVs (u0,v0)-(u1,v1), plain indices.
  let push4 (verts : ByteArray) (idx : ByteArray) (quads : Nat)
      (x0 y0 x1 y1 u0 v0 u1 v1 : Float32) (c : Color) :
      ByteArray × ByteArray := Id.run do
    let mut vs := verts
    vs := packTexVertex vs ⟨x0, y0⟩ ⟨u0, v0⟩ c
    vs := packTexVertex vs ⟨x1, y0⟩ ⟨u1, v0⟩ c
    vs := packTexVertex vs ⟨x0, y1⟩ ⟨u0, v1⟩ c
    vs := packTexVertex vs ⟨x1, y1⟩ ⟨u1, v1⟩ c
    let mut ix := idx
    let base := UInt32.ofNat (4 * quads)
    for j in ([0, 1, 2, 1, 3, 2] : List UInt32) do
      ix := pushU32 ix (base + j)
    return (vs, ix)
  let mut i := 0
  for l in layers do
    let (u, v) := match texs[i]? with
      | some lt =>
        (l.bounds.width / Float32.ofNat lt.w.toNat, l.bounds.height / Float32.ofNat lt.h.toNat)
      | none => (1, 1)
    let b := l.bounds
    let m := l.transform.getD .identity
    let c := Color.white.withAlpha l.alpha
    verts := packTexVertex verts (m.mapOffset ⟨b.left, b.top⟩) ⟨0, 0⟩ c
    verts := packTexVertex verts (m.mapOffset ⟨b.right, b.top⟩) ⟨u, 0⟩ c
    verts := packTexVertex verts (m.mapOffset ⟨b.left, b.bottom⟩) ⟨0, v⟩ c
    verts := packTexVertex verts (m.mapOffset ⟨b.right, b.bottom⟩) ⟨u, v⟩ c
    let base := UInt32.ofNat (4 * i)
    for j in ([0, 1, 2, 1, 3, 2] : List UInt32) do
      idx := pushU32 idx (base + j)
    i := i + 1
  quads := layers.size
  let some (tw, th, stw, sth) := snapshot | return (verts, idx)
  let sw := Float32.ofNat stw.toNat
  let sh := Float32.ofNat sth.toNat
  -- Snapshot blit: the target extent 1:1 (sampled nearest at replay).
  let (vs0, ix0) := push4 verts idx quads 0 0 tw th 0 0 (tw / sw) (th / sh) .white
  verts := vs0; idx := ix0
  quads := quads + 1
  for k in [0:backdrops.size] do
    let b := backdrops[k]!
    let some bt := btexs[k]? | break
    let r := b.region
    let w1 := backdropLevelDim r.width 1
    let h1 := backdropLevelDim r.height 1
    let aw := Float32.ofNat bt.aw.toNat
    let ah := Float32.ofNat bt.ah.toNat
    -- Downsample 1: the region's fraction of the snapshot (clamp-to-edge
    -- extends window-edge content past the texture) → the level-1 extent.
    let (vs1, ix1) := push4 verts idx quads 0 0 w1 h1
      (r.left / sw) (r.top / sh) (r.right / sw) (r.bottom / sh) .white
    verts := vs1; idx := ix1
    quads := quads + 1
    -- Downsample 2 (drawn only for two-halving panels): level 1 → level 2.
    let (vs2, ix2) := push4 verts idx quads 0 0
      (backdropLevelDim r.width 2) (backdropLevelDim r.height 2)
      0 0 (w1 / aw) (h1 / ah) .white
    verts := vs2; idx := ix2
    quads := quads + 1
    -- Panel composite: the panel rect addressed inside the blurred region at
    -- the final level, over the chain-end texture's pool dimensions.
    let scale := Float32.ofNat (2 ^ b.levels)
    let (_, ew, eh) := bt.final b.levels
    let ewf := Float32.ofNat ew.toNat
    let ehf := Float32.ofNat eh.toNat
    let p := b.panel
    let (vs3, ix3) := push4 verts idx quads p.left p.top p.right p.bottom
      ((p.left - r.left) / scale / ewf) ((p.top - r.top) / scale / ehf)
      ((p.right - r.left) / scale / ewf) ((p.bottom - r.top) / scale / ehf) .white
    verts := vs3; idx := ix3
    quads := quads + 1
  return (verts, idx)

/-- Clamp a scissor to the render-target extent (Metal validation requires
scissors inside the target; recorded clips can exceed it). -/
private def clampScissor (s : Sdl.Rect) (w h : Int32) : Sdl.Rect :=
  let x := max 0 s.x
  let y := max 0 s.y
  let r := min (s.x + s.w) w
  let b := min (s.y + s.h) h
  ⟨x, y, max 0 (r - x), max 0 (b - y)⟩

/-- Replay one command list into an open render pass: bind pipelines and
buffers lazily on kind switches, apply scissors on change, one draw per
command. `layerTexs` backs `.layer` composite commands; `layers` routes a
stretched layer's composite through the stretch pipeline (`cb` pushes its
per-draw fragment uniform — push uniforms bind to subsequent draws, legal
mid-pass, probe-verified). -/
private def replay (r : GpuRenderer) (rp : RenderPass) (cb : CommandBuffer)
    (cmds : Array DrawCmd) (layers : Array LayerEnc)
    (atlases : Array Texture) (layerTexs : Array LayerTex)
    (backdrops : Array BackdropEnc) (backdropTexs : Array BackdropTex)
    (imageTexs : Array Texture) (bufs : FrameBuffers) (w h : Int32) : IO Unit := do
  let full : Sdl.Rect := ⟨0, 0, w, h⟩
  -- 0 quad / 1 mesh / 2 glyph / 3 shadow / 4 layer / 5 image / 6 stretch /
  -- 7 backdrop / 8 glass (refracting backdrop) / 9 none
  let mut kind : Nat := 9
  let mut scissor : Option Sdl.Rect := none
  let mut atlas : Option Nat := none
  let mut boundLayer : Option (Nat × Bool) := none
  let mut boundImage : Option (Nat × Bool) := none
  let mut boundBackdrop : Option Nat := none
  -- What the layer pipeline's `LayerClip` fragment uniform currently holds:
  -- `none` = unknown (nothing pushed yet this replay, or clobbered by a
  -- stretch draw's `StretchParams` or a glass draw's `GlassParams` — same
  -- slot 0), `some rc` = `rc` pushed (`some none` = the unmasked sentinel).
  -- Fresh per replay entry: push uniforms persist on the command buffer
  -- across passes, so a new pass never trusts the slot's previous content.
  let mut pushedClip : Option (Option RoundRect) := none
  -- Which backdrop's `GlassParams` slot 0 holds (`none` = clobbered by any
  -- other slot-0 push, or nothing yet) — the glass twin of `pushedClip`.
  let mut pushedGlass : Option Nat := none
  for cmd in cmds do
    let want := match cmd with
      | .quads _ _ s | .mesh _ _ s | .glyphs _ _ _ s | .shadows _ _ s | .layer _ _ s
      | .image _ _ _ _ s | .backdrop _ s => s
    if want != scissor then
      rp.setScissor (clampScissor (want.getD full) w h)
      scissor := want
    match cmd with
    | .quads first count _ =>
      if kind != 0 then
        rp.bindPipeline r.pipelines.quad
        if let some s := bufs.quad then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        kind := 0
      rp.drawPrimitives 4 (UInt32.ofNat count) 0 (UInt32.ofNat first)
    | .mesh first count _ =>
      if kind != 1 then
        rp.bindPipeline r.pipelines.mesh
        if let some s := bufs.meshV then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        if let some s := bufs.meshI then
          rp.bindIndexBuffer { buffer := s.buffer } .u32
        kind := 1
      rp.drawIndexedPrimitives (UInt32.ofNat count) 1 (UInt32.ofNat first)
    | .glyphs first count atlasIdx _ =>
      if kind != 2 then
        rp.bindPipeline r.pipelines.glyph
        if let some s := bufs.glyphV then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        if let some s := bufs.glyphI then
          rp.bindIndexBuffer { buffer := s.buffer } .u32
        kind := 2
        atlas := none
      if atlas != some atlasIdx then
        if let some tex := atlases[atlasIdx]? then
          rp.bindFragmentSamplers 0 #[{ texture := tex, sampler := r.sampler }]
          atlas := some atlasIdx
      rp.drawIndexedPrimitives (UInt32.ofNat count) 1 (UInt32.ofNat first)
    | .shadows first count _ =>
      if kind != 3 then
        rp.bindPipeline r.pipelines.shadow
        if let some s := bufs.shadow then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        kind := 3
      rp.drawPrimitives 4 (UInt32.ofNat count) 0 (UInt32.ofNat first)
    | .layer idx linear _ =>
      match layers[idx]?.bind (·.stretch) with
      | some (sx, sy) =>
        -- Stretched composite: the layer buffers through the warping
        -- pipeline, always linear (the warp samples between texels); the
        -- per-draw fragment uniform carries the intensity plus the content's
        -- UV extent (the frag clamps to it, not the pooled texture edge).
        if kind != 6 then
          rp.bindPipeline r.pipelines.stretch
          if let some s := bufs.layerV then
            rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
          if let some s := bufs.layerI then
            rp.bindIndexBuffer { buffer := s.buffer } .u32
          kind := 6
          boundLayer := none
        if let some lt := layerTexs[idx]? then
          if boundLayer != some (idx, true) then
            rp.bindFragmentSamplers 0
              #[{ texture := lt.tex, sampler := r.samplerLinear }]
            boundLayer := some (idx, true)
          if let some l := layers[idx]? then
            cb.pushFragmentUniformData 0 (packStretchParams sx sy
              (l.bounds.width / Float32.ofNat lt.w.toNat)
              (l.bounds.height / Float32.ofNat lt.h.toNat))
            pushedClip := none    -- StretchParams clobbered slot 0
            pushedGlass := none
        rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * idx))
      | none =>
        if kind != 4 then
          rp.bindPipeline r.pipelines.layer
          if let some s := bufs.layerV then
            rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
          if let some s := bufs.layerI then
            rp.bindIndexBuffer { buffer := s.buffer } .u32
          kind := 4
          boundLayer := none
        if boundLayer != some (idx, linear) then
          if let some lt := layerTexs[idx]? then
            rp.bindFragmentSamplers 0
              #[{ texture := lt.tex, sampler := if linear then r.samplerLinear else r.sampler }]
            boundLayer := some (idx, linear)
        -- The composite's rounded mask (the sentinel when unmasked).
        let rc := layers[idx]?.bind (·.rounded)
        if pushedClip != some rc then
          cb.pushFragmentUniformData 0 (packLayerClip rc)
          pushedClip := some rc
          pushedGlass := none
        rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * idx))
    | .backdrop idx _ =>
      -- Backdrop panel composite: rides the layer pipeline (or the glass
      -- pipeline when the panel refracts) over the shared composite quad
      -- buffers, sampling the panel's blurred region texture linearly
      -- (low-res → panel-res upsample), masked by the record-site rounded
      -- clip. The quad sits at the fixed slot `layers.size + 3 idx + 3`
      -- (see `layerComposites`).
      let refracting : Bool := match backdrops[idx]? with
        | some b => decide (b.refr.strength > 0)
        | none => false
      let wantKind := if refracting then 8 else 7
      if kind != wantKind then
        rp.bindPipeline (if refracting then r.pipelines.glass else r.pipelines.layer)
        if let some s := bufs.layerV then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        if let some s := bufs.layerI then
          rp.bindIndexBuffer { buffer := s.buffer } .u32
        kind := wantKind
        boundBackdrop := none
      if boundBackdrop != some idx then
        if let some bt := backdropTexs[idx]? then
          let levels := (backdrops[idx]?.map (·.levels)).getD 1
          let (tex, _, _) := bt.final levels
          rp.bindFragmentSamplers 0 #[{ texture := tex, sampler := r.samplerLinear }]
          boundBackdrop := some idx
      if refracting then
        -- `GlassParams`: the panel's mask/refraction shape (its rounded
        -- clip, or the panel rect itself when unclipped — refraction needs
        -- a rim), the px→UV affine of the blurred region at its final
        -- downsample level, and the half-texel-inset valid-UV clamp.
        if pushedGlass != some idx then
          if let some b := backdrops[idx]? then
            if let some bt := backdropTexs[idx]? then
              let rr := b.rounded.getD (.ofRect b.panel)
              let scale := Float32.ofNat (2 ^ b.levels)
              let (_, ew, eh) := bt.final b.levels
              let ewf := Float32.ofNat ew.toNat
              let ehf := Float32.ofNat eh.toNat
              let sx := 1 / (scale * ewf)
              let sy := 1 / (scale * ehf)
              let wl := backdropLevelDim b.region.width b.levels
              let hl := backdropLevelDim b.region.height b.levels
              cb.pushFragmentUniformData 0 (packGlassParams rr
                sx sy (-b.region.left * sx) (-b.region.top * sy) b.refr
                (0.5 / ewf) (0.5 / ehf) ((wl - 0.5) / ewf) ((hl - 0.5) / ehf))
              pushedGlass := some idx
              pushedClip := none
      else
        let rc := backdrops[idx]?.bind (·.rounded)
        if pushedClip != some rc then
          cb.pushFragmentUniformData 0 (packLayerClip rc)
          pushedClip := some rc
          pushedGlass := none
      rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * (layers.size + 3 * idx + 3)))
    | .image first count tex linear _ =>
      -- Rides the layer pipeline (premultiplied sample × alpha) with its own
      -- vertex/index buffers, a per-command sampler choice, and the unmasked
      -- `LayerClip` sentinel (images clip by scissor only).
      if kind != 5 then
        rp.bindPipeline r.pipelines.layer
        if let some s := bufs.imageV then
          rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
        if let some s := bufs.imageI then
          rp.bindIndexBuffer { buffer := s.buffer } .u32
        kind := 5
        boundImage := none
      if pushedClip != some none then
        cb.pushFragmentUniformData 0 (packLayerClip none)
        pushedClip := some none
        pushedGlass := none
      if boundImage != some (tex, linear) then
        if let some t := imageTexs[tex]? then
          rp.bindFragmentSamplers 0
            #[{ texture := t, sampler := if linear then r.samplerLinear else r.sampler }]
          boundImage := some (tex, linear)
      rp.drawIndexedPrimitives (UInt32.ofNat count) 1 (UInt32.ofNat first)

/-- Resolve text, encode `list`, acquire the frame's pooled textures, grow
the frame buffers, and record the transfer-buffer write + copy pass on `cb`.
`tw × th` is the extent the target pass will render at (the snapshot texture
and its blit quad are sized from it — pass the window's pixel size on
screen, the offscreen extent otherwise). Returns the encoded frame, its
atlas texture table, and the frame textures, ready for
`GpuRenderer.passes`. -/
private def GpuRenderer.prepare (r : GpuRenderer) (cb : CommandBuffer)
    (list : DisplayList) (tw th : UInt32) :
    IO (EncodeResult × Array Texture × FrameTextures × Array Texture) := do
  let (texts, atlases) ← resolveTexts list
  let (imageIdxs, imageTexs) ← resolveImages r.dev cb list
  let enc := encode list texts imageIdxs
  -- Walk-order tripwire: the encoder consumes text runs and image indices by
  -- position, in exactly the order `resolveTexts`/`resolveImages` walked the
  -- list — a count mismatch means the walks drifted and prims were silently
  -- skipped. Loud on stderr always; fatal under `COMPOSE_GPU_DEBUG`.
  if enc.textsConsumed != texts.size || enc.imagesConsumed != imageIdxs.size then
    let msg := s!"Compose GPU: encode/resolve walk drift — \
      text runs {enc.textsConsumed} encoded vs {texts.size} resolved, \
      images {enc.imagesConsumed} encoded vs {imageIdxs.size} resolved"
    if gpuDebug then throw (IO.userError msg) else IO.eprintln msg
  let ftex ← acquireFrameTextures r
    (← r.dev.getSwapchainTextureFormat r.window) enc.layers
    (if enc.snapshotSplit.isSome then some (tw, th) else none) enc.backdrops
  frameStats.set { enc.stats with poolTextures := (← r.pool.get).size }
  let (lVerts, lIdx) := layerComposites enc.layers ftex.layers
    (ftex.snapshot.map fun (_, sw, sh) =>
      (Float32.ofNat tw.toNat, Float32.ofNat th.toNat, sw, sh))
    enc.backdrops ftex.backdrops
  -- Staging layout: one 16-byte-aligned region per pipeline buffer.
  let qOff := 0
  let shOff := qOff + align16 enc.quads.size
  let mvOff := shOff + align16 enc.shadows.size
  let miOff := mvOff + align16 enc.meshVerts.size
  let gvOff := miOff + align16 enc.meshIdx.size
  let giOff := gvOff + align16 enc.glyphVerts.size
  let lvOff := giOff + align16 enc.glyphIdx.size
  let liOff := lvOff + align16 lVerts.size
  let ivOff := liOff + align16 lIdx.size
  let iiOff := ivOff + align16 enc.imageVerts.size
  let total := iiOff + align16 enc.imageIdx.size
  if total > 0 then
    let mut bufs ← r.buffers.get
    bufs := { bufs with
      quad := ← ensureSlot r.dev bufs.quad .vertex enc.quads.size
      shadow := ← ensureSlot r.dev bufs.shadow .vertex enc.shadows.size
      meshV := ← ensureSlot r.dev bufs.meshV .vertex enc.meshVerts.size
      meshI := ← ensureSlot r.dev bufs.meshI .index enc.meshIdx.size
      glyphV := ← ensureSlot r.dev bufs.glyphV .vertex enc.glyphVerts.size
      glyphI := ← ensureSlot r.dev bufs.glyphI .index enc.glyphIdx.size
      layerV := ← ensureSlot r.dev bufs.layerV .vertex lVerts.size
      layerI := ← ensureSlot r.dev bufs.layerI .index lIdx.size
      imageV := ← ensureSlot r.dev bufs.imageV .vertex enc.imageVerts.size
      imageI := ← ensureSlot r.dev bufs.imageI .index enc.imageIdx.size }
    let tb ← match bufs.transfer with
      | some tb =>
        if tb.size.toNat ≥ total then pure tb
        else do
          tb.release
          pure (← r.dev.createTransferBuffer .upload
            (UInt32.ofNat (max 4096 total.nextPowerOfTwo)))
      | none =>
        pure (← r.dev.createTransferBuffer .upload
          (UInt32.ofNat (max 4096 total.nextPowerOfTwo)))
    bufs := { bufs with transfer := some tb }
    r.buffers.set bufs
    -- Each region writes straight into the transfer buffer at its offset (no
    -- staging concatenation). The first write cycles — the previous frame's
    -- copy pass may still be reading the old backing — and the rest must NOT
    -- cycle again (another cycle would swap away the regions just written).
    -- Alignment gaps are never uploaded, so they can stay stale.
    let mut cycled := false
    for (off, bytes) in [(qOff, enc.quads), (shOff, enc.shadows),
                         (mvOff, enc.meshVerts), (miOff, enc.meshIdx),
                         (gvOff, enc.glyphVerts), (giOff, enc.glyphIdx),
                         (lvOff, lVerts), (liOff, lIdx),
                         (ivOff, enc.imageVerts), (iiOff, enc.imageIdx)] do
      unless bytes.isEmpty do
        tb.write bytes (dstOffset := UInt32.ofNat off) (cycle := !cycled)
        cycled := true
    let cp ← cb.beginCopyPass
    uploadRegion cp tb qOff enc.quads bufs.quad
    uploadRegion cp tb shOff enc.shadows bufs.shadow
    uploadRegion cp tb mvOff enc.meshVerts bufs.meshV
    uploadRegion cp tb miOff enc.meshIdx bufs.meshI
    uploadRegion cp tb gvOff enc.glyphVerts bufs.glyphV
    uploadRegion cp tb giOff enc.glyphIdx bufs.glyphI
    uploadRegion cp tb lvOff lVerts bufs.layerV
    uploadRegion cp tb liOff lIdx bufs.layerI
    uploadRegion cp tb ivOff enc.imageVerts bufs.imageV
    uploadRegion cp tb iiOff enc.imageIdx bufs.imageI
    cp.finish
  return (enc, atlases, ftex, imageTexs)

/-- Record one backdrop panel's downsample + separable-blur passes off the
snapshot texture `stex`: a layer-pipeline **copy** draw of composite quad
`quadBase` (the panel's region → the level-1 extent of `bt.a`, bilinear ≈ a
2× box filter), a second halving into `bt.b` past σ 32 (quad `quadBase + 1`),
then the H/V Gaussian round-trip at `σ / 2^levels` — H into the *other*
texture, V back into the chain's end, where `BackdropTex.final` points the
composite. Every `cycle := true` target's prior content was only read by
passes recorded earlier on this command buffer (the M-i layer-blur
pattern). -/
private def GpuRenderer.backdropPasses (r : GpuRenderer) (cb : CommandBuffer)
    (bufs : FrameBuffers) (stex : Texture) (quadBase : Nat)
    (b : BackdropEnc) (bt : BackdropTex) : IO Unit := do
  let aw := Float32.ofNat bt.aw.toNat
  let ah := Float32.ofNat bt.ah.toNat
  let bw := Float32.ofNat bt.bw.toNat
  let bh := Float32.ofNat bt.bh.toNat
  let copy (dst : Texture) (dw dh : Float32) (src : Texture) (quadIdx : Nat) :
      IO Unit := do
    cb.pushVertexUniformData 0 (packGlobals dw dh)
    let rp ← cb.beginRenderPass
      #[{ texture := dst, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
          cycle := true }]
    rp.bindPipeline r.pipelines.layer
    if let some s := bufs.layerV then
      rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
    if let some s := bufs.layerI then
      rp.bindIndexBuffer { buffer := s.buffer } .u32
    rp.bindFragmentSamplers 0 #[{ texture := src, sampler := r.samplerLinear }]
    cb.pushFragmentUniformData 0 (packLayerClip none)
    rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * quadIdx))
    rp.finish
  copy bt.a aw ah stex quadBase
  if b.levels ≥ 2 then
    copy bt.b bw bh bt.a (quadBase + 1)
  let wl := backdropLevelDim b.region.width b.levels
  let hl := backdropLevelDim b.region.height b.levels
  let sigma := b.sigma / Float32.ofNat (2 ^ b.levels)
  let taps := Float32.ofNat (min 48 (max 1 (3 * sigma).ceil.toUInt32.toNat))
  let (fin, finW, finH, other, otherW, otherH) :=
    if b.levels % 2 == 1 then (bt.a, aw, ah, bt.b, bw, bh)
    else (bt.b, bw, bh, bt.a, aw, ah)
  cb.pushVertexUniformData 0 (packBlurVert otherW otherH wl hl (wl / finW) (hl / finH))
  cb.pushFragmentUniformData 0 (packBlurParams (1 / finW) 0 sigma taps)
  let hp ← cb.beginRenderPass
    #[{ texture := other, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
        cycle := true }]
  hp.bindPipeline r.pipelines.blur
  hp.bindFragmentSamplers 0 #[{ texture := fin, sampler := r.samplerLinear }]
  hp.drawPrimitives 4 1 0 0
  hp.finish
  cb.pushVertexUniformData 0 (packBlurVert finW finH wl hl (wl / otherW) (hl / otherH))
  cb.pushFragmentUniformData 0 (packBlurParams 0 (1 / otherH) sigma taps)
  let vp ← cb.beginRenderPass
    #[{ texture := fin, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
        cycle := true }]
  vp.bindPipeline r.pipelines.blur
  vp.bindFragmentSamplers 0 #[{ texture := other, sampler := r.samplerLinear }]
  vp.drawPrimitives 4 1 0 0
  vp.finish

/-- Record the frame's render passes on `cb`: one transparent-cleared pass
per offscreen layer (innermost-first — composites of inner layers replay
inside outer ones), plus two separable Gaussian passes per *blurred* layer
(content → ping → content, so the composite samples the content texture
unchanged); then the target work. Without backdrops that is one
clear-and-replay pass into `target`; with them, the **progressive
snapshot**: the target list composes into the pooled snapshot texture
segment by segment — the prefix behind the first panel into a cleared pass
(the frame's clear color — it *is* the frame background), then per panel
`backdropPasses` off the snapshot as painted so far followed by a reopened
(`loadOp .load`) pass replaying from that panel's `.backdrop` composite to
the next boundary — and the target pass clears and blits the snapshot 1:1
nearest. Every command still draws exactly once, and each panel frosts
everything beneath it, earlier panels' frost included (the demo-glass
scroll bug: a glass card mid-scroll must not blind later panels to content
drawn after it). Each pass pushes its own `Globals`
viewport so NDC maps to its texture's extent (blur passes push their
`BlurVert`/`BlurParams` pair instead; a *stretched* layer needs no extra
pass — its composite draw runs the stretch pipeline, pushing
`StretchParams` mid-pass). -/
private def GpuRenderer.passes (r : GpuRenderer) (cb : CommandBuffer)
    (target : Texture) (w h : UInt32) (clear : Color) (enc : EncodeResult)
    (atlases : Array Texture) (ftex : FrameTextures)
    (imageTexs : Array Texture) : IO Unit := do
  let bufs ← r.buffers.get
  let mut i := 0
  for l in enc.layers do
    if let some lt := ftex.layers[i]? then
      cb.pushVertexUniformData 0
        (packGlobals (Float32.ofNat lt.w.toNat) (Float32.ofNat lt.h.toNat))
      -- `cycle`: the pooled texture is reused every frame; with two frames in
      -- flight the previous frame may still be sampling it — cycling swaps in
      -- fresh backing at pass begin (loadOp is `.clear`, so nothing is lost).
      let rp ← cb.beginRenderPass
        #[{ texture := lt.tex, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
            cycle := true }]
      replay r rp cb l.cmds enc.layers atlases ftex.layers
        enc.backdrops ftex.backdrops imageTexs bufs
        (Int32.ofNat lt.w.toNat) (Int32.ofNat lt.h.toNat)
      rp.finish
      if l.sigma > 0 then
        if let some ping := lt.blurTex then
          -- Separable Gaussian: H blurs content → ping, V blurs ping → back
          -- into the content texture (its `cycle` is safe — the V pass fully
          -- rewrites it before anything recorded later samples it; the H
          -- pass's read of the pre-cycle backing was recorded earlier).
          -- Regions outside the content extent are cleared transparent, so
          -- the taps' clamp-to-edge never reads stale texels.
          let bw := l.bounds.width
          let bh := l.bounds.height
          let taps := Float32.ofNat (min 48 (max 1 (3 * l.sigma).ceil.toUInt32.toNat))
          let texW := Float32.ofNat lt.w.toNat
          let texH := Float32.ofNat lt.h.toNat
          let pingW := Float32.ofNat lt.blurW.toNat
          let pingH := Float32.ofNat lt.blurH.toNat
          cb.pushVertexUniformData 0 (packBlurVert pingW pingH bw bh (bw / texW) (bh / texH))
          cb.pushFragmentUniformData 0 (packBlurParams (1 / texW) 0 l.sigma taps)
          let hp ← cb.beginRenderPass
            #[{ texture := ping, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
                cycle := true }]
          hp.bindPipeline r.pipelines.blur
          hp.bindFragmentSamplers 0 #[{ texture := lt.tex, sampler := r.samplerLinear }]
          hp.drawPrimitives 4 1 0 0
          hp.finish
          cb.pushVertexUniformData 0 (packBlurVert texW texH bw bh (bw / pingW) (bh / pingH))
          cb.pushFragmentUniformData 0 (packBlurParams 0 (1 / pingH) l.sigma taps)
          let vp ← cb.beginRenderPass
            #[{ texture := lt.tex, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
                cycle := true }]
          vp.bindPipeline r.pipelines.blur
          vp.bindFragmentSamplers 0 #[{ texture := ping, sampler := r.samplerLinear }]
          vp.drawPrimitives 4 1 0 0
          vp.finish
    i := i + 1
  match enc.snapshotSplit, ftex.snapshot with
  | some split, some (stex, sw, sh) =>
    -- Progressive snapshot: the whole scene composes into S, segment by
    -- segment. The `.backdrop` command positions are the boundaries (the
    -- first is `split` by construction; command `cuts[k]` carries index
    -- `k` — backdrops append in command order).
    let mut cuts : Array Nat := #[]
    for ci in [0:enc.cmds.size] do
      if let some (.backdrop ..) := enc.cmds[ci]? then
        cuts := cuts.push ci
    let globals := packGlobals (Float32.ofNat sw.toNat) (Float32.ofNat sh.toNat)
    -- Segment 0 — the scene behind the first panel — into S, cleared to the
    -- frame's clear color (it *is* the frame background). The one cycle:
    -- later passes reopen the same backing with `loadOp .load`.
    cb.pushVertexUniformData 0 globals
    let sp ← cb.beginRenderPass
      #[{ texture := stex, loadOp := .clear
          clearColor := ⟨clear.r, clear.g, clear.b, clear.a⟩, cycle := true }]
    replay r sp cb (enc.cmds.extract 0 split) enc.layers atlases ftex.layers
      enc.backdrops ftex.backdrops imageTexs bufs
      (Int32.ofNat sw.toNat) (Int32.ofNat sh.toNat)
    sp.finish
    -- Per panel: blur its region off S *as painted so far*, then reopen S
    -- and replay from the `.backdrop` composite up to the next boundary —
    -- so each panel frosts everything beneath it, earlier panels' frost
    -- included, and every command still draws exactly once.
    let mut k := 0
    for pos in cuts do
      if let some b := enc.backdrops[k]? then
        if let some bt := ftex.backdrops[k]? then
          r.backdropPasses cb bufs stex (enc.layers.size + 1 + 3 * k) b bt
      let stop := cuts[k + 1]?.getD enc.cmds.size
      cb.pushVertexUniformData 0 globals   -- the blur passes clobbered it
      let sp ← cb.beginRenderPass #[{ texture := stex, loadOp := .load }]
      replay r sp cb (enc.cmds.extract pos stop) enc.layers atlases
        ftex.layers enc.backdrops ftex.backdrops imageTexs bufs
        (Int32.ofNat sw.toNat) (Int32.ofNat sh.toNat)
      sp.finish
      k := k + 1
    -- Target pass: clear → blit S 1:1 (nearest — byte-exact).
    cb.pushVertexUniformData 0
      (packGlobals (Float32.ofNat w.toNat) (Float32.ofNat h.toNat))
    let rp ← cb.beginRenderPass
      #[{ texture := target, loadOp := .clear
          clearColor := ⟨clear.r, clear.g, clear.b, clear.a⟩ }]
    rp.bindPipeline r.pipelines.layer
    if let some s := bufs.layerV then
      rp.bindVertexBuffers 0 #[{ buffer := s.buffer }]
    if let some s := bufs.layerI then
      rp.bindIndexBuffer { buffer := s.buffer } .u32
    rp.bindFragmentSamplers 0 #[{ texture := stex, sampler := r.sampler }]
    cb.pushFragmentUniformData 0 (packLayerClip none)
    rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * enc.layers.size))
    rp.finish
  | _, _ =>
    cb.pushVertexUniformData 0
      (packGlobals (Float32.ofNat w.toNat) (Float32.ofNat h.toNat))
    let rp ← cb.beginRenderPass
      #[{ texture := target, loadOp := .clear
          clearColor := ⟨clear.r, clear.g, clear.b, clear.a⟩ }]
    replay r rp cb enc.cmds enc.layers atlases ftex.layers
      enc.backdrops ftex.backdrops imageTexs bufs
      (Int32.ofNat w.toNat) (Int32.ofNat h.toNat)
    rp.finish

/-- One-shot breadcrumbs for the process's very first on-screen render —
the stage reached pinpoints where a broken device/driver stalls (e.g. a
swapchain acquire that never returns), which is otherwise undebuggable
from a phone's logcat. -/
private initialize firstRenderTrace : IO.Ref Bool ← IO.mkRef true

/-- Render one frame: returns `false` when no swapchain texture was available
(the caller re-arms a frame request), `true` after a successful submit. -/
def GpuRenderer.render (r : GpuRenderer) (clear : Color) (list : DisplayList)
    (mayBlock : Bool) : IO Bool := do
  let trace ← firstRenderTrace.modifyGet fun b => (b, false)
  if trace then
    Sdl.logInfo (msg := s!"Compose GPU: first render — prepare (mayBlock {mayBlock})")
  let cb ← r.dev.acquireCommandBuffer
  -- The window's pixel size stands in for the swapchain extent (not yet
  -- acquired): it sizes the snapshot texture and its blit quad. A transient
  -- mismatch mid-resize misblits one frame — the next frame corrects.
  let (pw, ph) ← r.window.getSizeInPixels
  -- An abandoned command buffer leaks (its finalizer only drops the device
  -- ref — submit/cancel are unsafe from finalizers): if preparing throws
  -- (e.g. texture/buffer creation under memory pressure), cancel before
  -- rethrowing so a retried frame doesn't leak one buffer per attempt.
  -- Canceling is legal here — no swapchain texture has been acquired yet.
  let (enc, atlases, ftex, imageTexs) ←
    try
      r.prepare cb list (UInt32.ofNat (max 1 pw.toNatClampNeg))
        (UInt32.ofNat (max 1 ph.toNatClampNeg))
    catch e => cb.cancel; throw e
  if trace then
    Sdl.logInfo (msg := "Compose GPU: first render — acquiring swapchain texture")
  let sc? ←
    try
      if mayBlock then cb.waitAndAcquireSwapchainTexture r.window
      else cb.acquireSwapchainTexture r.window
    catch e => cb.cancel; throw e
  match sc? with
  | none =>
    if trace then
      Sdl.logInfo (msg := "Compose GPU: first render — no swapchain texture")
    cb.submit
    return false
  | some sc =>
    if trace then
      Sdl.logInfo (msg := s!"Compose GPU: first render — acquired {sc.width}x{sc.height}, submitting")
    r.passes cb sc.texture sc.width sc.height clear enc atlases ftex imageTexs
    cb.submit
    return true

/-- Render `list` into a fresh offscreen texture of the window's swapchain
format and read the pixels back (tightly packed rows, 4 bytes per pixel in
the swapchain format's channel order). Synchronous — drives the pixel asserts
in `gpu-probe` and the M-d GPU-vs-SDL parity diff. -/
def GpuRenderer.renderOffscreen (r : GpuRenderer) (clear : Color)
    (list : DisplayList) (w h : Nat) : IO ByteArray := do
  let fmt ← r.dev.getSwapchainTextureFormat r.window
  let tex ← r.dev.createTexture
    { format := fmt, usage := .colorTarget
      width := UInt32.ofNat w, height := UInt32.ofNat h }
  let dl ← r.dev.createTransferBuffer .download (UInt32.ofNat (w * h * 4))
  let cb ← r.dev.acquireCommandBuffer
  -- Same leak guard as `render`: cancel the un-submitted command buffer (and
  -- release this call's private textures) if recording throws.
  try
    let (enc, atlases, ftex, imageTexs) ←
      r.prepare cb list (UInt32.ofNat w) (UInt32.ofNat h)
    r.passes cb tex (UInt32.ofNat w) (UInt32.ofNat h) clear enc atlases ftex imageTexs
    let cp ← cb.beginCopyPass
    cp.downloadFromTexture
      { texture := tex, w := UInt32.ofNat w, h := UInt32.ofNat h }
      { buffer := dl }
    cp.finish
  catch e =>
    cb.cancel
    tex.release
    dl.release
    throw e
  let fence ← cb.submitAndAcquireFence
  r.dev.waitForFences true #[fence]
  let bytes ← dl.read
  tex.release
  dl.release
  return bytes

/-- Drop the renderer's per-window device caches — pooled layer textures and
the grown frame/transfer buffers; everything rebuilds lazily on the next
frame. SDL defers destruction of anything still referenced by in-flight
frames, so no idle-wait is needed. Together with `dropImageTexCache` this
implements the GPU backend's `RenderBackend.invalidateCaches` (`lowMemory`
and the renderer-reset events); it is also the whole of `dispose`. -/
def GpuRenderer.invalidateCaches (r : GpuRenderer) : IO Unit := do
  for e in (← r.pool.get) do
    e.tex.release
  r.pool.set #[]
  let bufs ← r.buffers.get
  for s in [bufs.quad, bufs.shadow, bufs.meshV, bufs.meshI,
            bufs.glyphV, bufs.glyphI, bufs.layerV, bufs.layerI,
            bufs.imageV, bufs.imageI] do
    if let some s := s then
      s.buffer.release
  if let some tb := bufs.transfer then
    tb.release
  r.buffers.set {}

/-- Release the renderer's per-window GPU resources (pooled layer textures,
frame/transfer buffers). SDL defers destruction of anything still referenced
by in-flight frames; call before releasing the window. -/
def GpuRenderer.dispose (r : GpuRenderer) : IO Unit :=
  r.invalidateCaches

end Compose.Draw.Gpu

end
