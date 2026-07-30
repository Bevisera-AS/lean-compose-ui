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
(pure) → acquire layer textures from the pool + grow GPU buffers (2×, never
shrink) → one transfer-buffer write + copy pass (`cycle := true` throughout —
probe-verified to preserve in-flight data) → acquire the swapchain texture
(blocking or not per `mayBlock`; `none` still submits the copy work and
reports a skipped frame) → one render pass per offscreen layer
(innermost-first, cleared transparent; blurred layers append two separable
Gaussian passes bouncing through a second pooled texture) then the target
pass, each replaying its command list → submit (present is implicit).

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

/-- Acquire the pooled textures of every encoded layer (blurred layers take a
second, ping texture for the separable passes), then age and trim the pool:
entries idle past `poolTrimAge` frames are released. Parallel to `layers`. -/
private def acquireLayerTextures (r : GpuRenderer) (fmt : TextureFormat)
    (layers : Array LayerEnc) : IO (Array LayerTex) := do
  let mut pool := (← r.pool.get).map fun e => { e with used := false }
  let mut out : Array LayerTex := Array.emptyWithCapacity layers.size
  for l in layers do
    let w := quantize64 l.bounds.width
    let h := quantize64 l.bounds.height
    let (pool', tex, tw, th) ← poolAcquire r.dev fmt pool w h
    pool := pool'
    if l.sigma > 0 then
      let (pool'', btex, bw, bh) ← poolAcquire r.dev fmt pool w h
      pool := pool''
      out := out.push { tex, w := tw, h := th, blurTex := some btex, blurW := bw, blurH := bh }
    else
      out := out.push { tex, w := tw, h := th }
  let mut kept : Array PoolEntry := #[]
  for e in pool do
    if e.used then
      kept := kept.push e
    else if e.idle + 1 ≥ poolTrimAge then
      e.tex.release
    else
      kept := kept.push { e with idle := e.idle + 1 }
  r.pool.set kept
  return out

/-- The packed composite quads of the frame's layers: layer `i` owns vertices
`4i..4i+3` and indices `6i..6i+5` (so `DrawCmd.layer i` draws at a fixed
offset), positioned at the layer bounds' corners mapped through the composite
transform (a transformed layer renders axis-aligned into its texture; only
this quad rotates/scales), with UVs covering the content's fraction of the
pooled texture and the group alpha in the vertex color. -/
private def layerComposites (layers : Array LayerEnc)
    (texs : Array LayerTex) : ByteArray × ByteArray := Id.run do
  let mut verts := ByteArray.empty
  let mut idx := ByteArray.empty
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
    (imageTexs : Array Texture) (bufs : FrameBuffers) (w h : Int32) : IO Unit := do
  let full : Sdl.Rect := ⟨0, 0, w, h⟩
  -- 0 quad / 1 mesh / 2 glyph / 3 shadow / 4 layer / 5 image / 6 stretch /
  -- 9 none
  let mut kind : Nat := 9
  let mut scissor : Option Sdl.Rect := none
  let mut atlas : Option Nat := none
  let mut boundLayer : Option (Nat × Bool) := none
  let mut boundImage : Option (Nat × Bool) := none
  -- What the layer pipeline's `LayerClip` fragment uniform currently holds:
  -- `none` = unknown (nothing pushed yet this replay, or clobbered by a
  -- stretch draw's `StretchParams` — same slot 0), `some rc` = `rc` pushed
  -- (`some none` = the unmasked sentinel). Fresh per replay entry: push
  -- uniforms persist on the command buffer across passes, so a new pass
  -- never trusts the slot's previous content.
  let mut pushedClip : Option (Option RoundRect) := none
  for cmd in cmds do
    let want := match cmd with
      | .quads _ _ s | .mesh _ _ s | .glyphs _ _ _ s | .shadows _ _ s | .layer _ _ s
      | .image _ _ _ _ s => s
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
        rp.drawIndexedPrimitives 6 1 (UInt32.ofNat (6 * idx))
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
      if boundImage != some (tex, linear) then
        if let some t := imageTexs[tex]? then
          rp.bindFragmentSamplers 0
            #[{ texture := t, sampler := if linear then r.samplerLinear else r.sampler }]
          boundImage := some (tex, linear)
      rp.drawIndexedPrimitives (UInt32.ofNat count) 1 (UInt32.ofNat first)

/-- Resolve text, encode `list`, acquire the frame's layer textures, grow the
frame buffers, and record the transfer-buffer write + copy pass on `cb`.
Returns the encoded frame, its atlas texture table, and the layer textures,
ready for `GpuRenderer.passes`. -/
private def GpuRenderer.prepare (r : GpuRenderer) (cb : CommandBuffer)
    (list : DisplayList) :
    IO (EncodeResult × Array Texture × Array LayerTex × Array Texture) := do
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
  frameStats.set enc.stats
  let layerTexs ← acquireLayerTextures r
    (← r.dev.getSwapchainTextureFormat r.window) enc.layers
  let (lVerts, lIdx) := layerComposites enc.layers layerTexs
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
  return (enc, atlases, layerTexs, imageTexs)

/-- Record the frame's render passes on `cb`: one transparent-cleared pass
per offscreen layer (innermost-first — composites of inner layers replay
inside outer ones), plus two separable Gaussian passes per *blurred* layer
(content → ping → content, so the composite samples the content texture
unchanged), then the clear-and-replay pass into `target`. Each pass pushes
its own `Globals` viewport so NDC maps to its texture's extent (blur passes
push their `BlurVert`/`BlurParams` pair instead; a *stretched* layer needs
no extra pass — its composite draw runs the stretch pipeline, pushing
`StretchParams` mid-pass). -/
private def GpuRenderer.passes (r : GpuRenderer) (cb : CommandBuffer)
    (target : Texture) (w h : UInt32) (clear : Color) (enc : EncodeResult)
    (atlases : Array Texture) (layerTexs : Array LayerTex)
    (imageTexs : Array Texture) : IO Unit := do
  let bufs ← r.buffers.get
  let mut i := 0
  for l in enc.layers do
    if let some lt := layerTexs[i]? then
      cb.pushVertexUniformData 0
        (packGlobals (Float32.ofNat lt.w.toNat) (Float32.ofNat lt.h.toNat))
      -- `cycle`: the pooled texture is reused every frame; with two frames in
      -- flight the previous frame may still be sampling it — cycling swaps in
      -- fresh backing at pass begin (loadOp is `.clear`, so nothing is lost).
      let rp ← cb.beginRenderPass
        #[{ texture := lt.tex, loadOp := .clear, clearColor := ⟨0, 0, 0, 0⟩
            cycle := true }]
      replay r rp cb l.cmds enc.layers atlases layerTexs imageTexs bufs
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
  cb.pushVertexUniformData 0
    (packGlobals (Float32.ofNat w.toNat) (Float32.ofNat h.toNat))
  let rp ← cb.beginRenderPass
    #[{ texture := target, loadOp := .clear
        clearColor := ⟨clear.r, clear.g, clear.b, clear.a⟩ }]
  replay r rp cb enc.cmds enc.layers atlases layerTexs imageTexs bufs
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
  -- An abandoned command buffer leaks (its finalizer only drops the device
  -- ref — submit/cancel are unsafe from finalizers): if preparing throws
  -- (e.g. texture/buffer creation under memory pressure), cancel before
  -- rethrowing so a retried frame doesn't leak one buffer per attempt.
  -- Canceling is legal here — no swapchain texture has been acquired yet.
  let (enc, atlases, layerTexs, imageTexs) ←
    try r.prepare cb list
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
    r.passes cb sc.texture sc.width sc.height clear enc atlases layerTexs imageTexs
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
    let (enc, atlases, layerTexs, imageTexs) ← r.prepare cb list
    r.passes cb tex (UInt32.ofNat w) (UInt32.ofNat h) clear enc atlases layerTexs imageTexs
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
