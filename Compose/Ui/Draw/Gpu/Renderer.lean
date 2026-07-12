import Compose.Ui.Draw.Gpu.Encode
import Compose.Ui.Draw.Gpu.Shaders
import Compose.Ui.Draw.Gpu.TextEngine

/-!
# GPU frame renderer (`Compose/Ui/Draw/Gpu/Renderer.lean`)

Per-window GPU state and the frame lifecycle: resolve text (IO) → encode
(pure) → grow GPU buffers (2×, never shrink) → one transfer-buffer write +
copy pass (`cycle := true` throughout — probe-verified to preserve in-flight
data) → acquire the swapchain texture (blocking or not per `mayBlock`;
`none` still submits the copy work and reports a skipped frame) → one render
pass replaying the command list → submit (present is implicit).

One `Gpu.Device` is shared per process (lazily created, claiming every GPU
window); pipelines and the sampler live in this structure so they stay
reachable while bound (SDL binds do not retain them).
-/

namespace Compose.Draw.Gpu
open Sdl.Gpu

/-- The process-wide GPU device (SDL_GPU supports one device claiming many
windows; MSL shader format, debug mode via `COMPOSE_GPU_DEBUG`). -/
private initialize deviceRef : IO.Ref (Option Device) ← IO.mkRef none

/-- The shared device, created on first use. Throws where SDL_GPU has no
backend (always under the dummy video driver — the GPU backend is real-driver
only). -/
def getDevice : IO Device := do
  if let some d := ← deviceRef.get then
    return d
  let debug := (← IO.getEnv "COMPOSE_GPU_DEBUG").isSome
  let d ← createDevice .msl (debugMode := debug)
  d.setAllowedFramesInFlight 2
  deviceRef.set (some d)
  return d

/-- One GPU buffer with its current byte capacity. -/
private structure Slot where
  buffer : Buffer
  capacity : Nat

/-- Per-window frame buffers, grown geometrically and never shrunk. -/
private structure FrameBuffers where
  quad : Option Slot := none
  meshV : Option Slot := none
  meshI : Option Slot := none
  glyphV : Option Slot := none
  glyphI : Option Slot := none
  transfer : Option TransferBuffer := none

/-- Per-window GPU renderer state. -/
structure GpuRenderer where
  /-- The shared device. -/
  dev : Device
  /-- The claimed window. -/
  window : Sdl.Window
  /-- Pipelines against the window's swapchain format (kept reachable —
  binds do not retain). -/
  pipelines : Pipelines
  /-- Glyph-atlas sampler (nearest — glyphs are drawn 1:1 pixel-snapped). -/
  sampler : Sampler
  /-- Frame buffers (mutable: grown across frames). -/
  private buffers : IO.Ref FrameBuffers

/-- Create the per-window renderer state for an already-claimed window. -/
def GpuRenderer.create (dev : Device) (window : Sdl.Window) : IO GpuRenderer := do
  let fmt ← dev.getSwapchainTextureFormat window
  return { dev, window
           pipelines := ← Pipelines.create dev fmt
           sampler := ← dev.createSampler
             { minFilter := .nearest, magFilter := .nearest
               addressModeU := .clampToEdge, addressModeV := .clampToEdge
               addressModeW := .clampToEdge }
           buffers := ← IO.mkRef {} }

/-- Round `n` up to a 16-byte boundary (transfer-region alignment). -/
private def align16 (n : Nat) : Nat := (n + 15) / 16 * 16

/-- Pad `b` with zeros up to `size` bytes. -/
private def padTo (b : ByteArray) (size : Nat) : ByteArray := Id.run do
  let mut b := b
  for _ in [0:size - b.size] do
    b := b.push 0
  return b

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

/-- Clamp a scissor to the render-target extent (Metal validation requires
scissors inside the target; recorded clips can exceed it). -/
private def clampScissor (s : Sdl.Rect) (w h : Int32) : Sdl.Rect :=
  let x := max 0 s.x
  let y := max 0 s.y
  let r := min (s.x + s.w) w
  let b := min (s.y + s.h) h
  ⟨x, y, max 0 (r - x), max 0 (b - y)⟩

/-- Replay the encoded command list into an open render pass: bind pipelines
and buffers lazily on kind switches, apply scissors on change, one draw per
command. -/
private def replay (r : GpuRenderer) (rp : RenderPass) (enc : EncodeResult)
    (atlases : Array Texture) (bufs : FrameBuffers) (w h : Int32) : IO Unit := do
  let full : Sdl.Rect := ⟨0, 0, w, h⟩
  let mut kind : Nat := 3       -- 0 quad / 1 mesh / 2 glyph / 3 none
  let mut scissor : Option Sdl.Rect := none
  let mut atlas : Option Nat := none
  for cmd in enc.cmds do
    let want := match cmd with
      | .quads _ _ s | .mesh _ _ s | .glyphs _ _ _ s => s
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

/-- Resolve text, encode `list`, grow the frame buffers, and record the
transfer-buffer write + copy pass on `cb`. Returns the encoded frame and its
atlas texture table, ready for `GpuRenderer.pass`. -/
private def GpuRenderer.prepare (r : GpuRenderer) (cb : CommandBuffer)
    (list : DisplayList) : IO (EncodeResult × Array Texture) := do
  let (texts, atlases) ← resolveTexts list
  let enc := encode list texts
  -- Staging layout: one 16-byte-aligned region per pipeline buffer.
  let qOff := 0
  let mvOff := qOff + align16 enc.quads.size
  let miOff := mvOff + align16 enc.meshVerts.size
  let gvOff := miOff + align16 enc.meshIdx.size
  let giOff := gvOff + align16 enc.glyphVerts.size
  let total := giOff + align16 enc.glyphIdx.size
  if total > 0 then
    let mut bufs ← r.buffers.get
    bufs := { bufs with
      quad := ← ensureSlot r.dev bufs.quad .vertex enc.quads.size
      meshV := ← ensureSlot r.dev bufs.meshV .vertex enc.meshVerts.size
      meshI := ← ensureSlot r.dev bufs.meshI .index enc.meshIdx.size
      glyphV := ← ensureSlot r.dev bufs.glyphV .vertex enc.glyphVerts.size
      glyphI := ← ensureSlot r.dev bufs.glyphI .index enc.glyphIdx.size }
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
    let staging :=
      padTo (padTo (padTo (padTo (padTo enc.quads mvOff ++ enc.meshVerts) miOff
        ++ enc.meshIdx) gvOff ++ enc.glyphVerts) giOff ++ enc.glyphIdx) total
    tb.write staging (cycle := true)
    let cp ← cb.beginCopyPass
    uploadRegion cp tb qOff enc.quads bufs.quad
    uploadRegion cp tb mvOff enc.meshVerts bufs.meshV
    uploadRegion cp tb miOff enc.meshIdx bufs.meshI
    uploadRegion cp tb gvOff enc.glyphVerts bufs.glyphV
    uploadRegion cp tb giOff enc.glyphIdx bufs.glyphI
    cp.finish
  return (enc, atlases)

/-- Record the clear-and-replay render pass into `target` on `cb`. -/
private def GpuRenderer.pass (r : GpuRenderer) (cb : CommandBuffer)
    (target : Texture) (w h : UInt32) (clear : Color) (enc : EncodeResult)
    (atlases : Array Texture) : IO Unit := do
  cb.pushVertexUniformData 0
    (packGlobals (Float32.ofNat w.toNat) (Float32.ofNat h.toNat))
  let rp ← cb.beginRenderPass
    #[{ texture := target, loadOp := .clear
        clearColor := ⟨clear.r, clear.g, clear.b, clear.a⟩ }]
  replay r rp enc atlases (← r.buffers.get)
    (Int32.ofNat w.toNat) (Int32.ofNat h.toNat)
  rp.finish

/-- Render one frame: returns `false` when no swapchain texture was available
(the caller re-arms a frame request), `true` after a successful submit. -/
def GpuRenderer.render (r : GpuRenderer) (clear : Color) (list : DisplayList)
    (mayBlock : Bool) : IO Bool := do
  let cb ← r.dev.acquireCommandBuffer
  let (enc, atlases) ← r.prepare cb list
  let sc? ← if mayBlock then cb.waitAndAcquireSwapchainTexture r.window
            else cb.acquireSwapchainTexture r.window
  match sc? with
  | none =>
    cb.submit
    return false
  | some sc =>
    r.pass cb sc.texture sc.width sc.height clear enc atlases
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
  let (enc, atlases) ← r.prepare cb list
  r.pass cb tex (UInt32.ofNat w) (UInt32.ofNat h) clear enc atlases
  let cp ← cb.beginCopyPass
  cp.downloadFromTexture
    { texture := tex, w := UInt32.ofNat w, h := UInt32.ofNat h }
    { buffer := dl }
  cp.finish
  let fence ← cb.submitAndAcquireFence
  r.dev.waitForFences true #[fence]
  let bytes ← dl.read
  tex.release
  dl.release
  return bytes

end Compose.Draw.Gpu
