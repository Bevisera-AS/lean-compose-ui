import Compose

/-!
# gpu-probe (`Demos/GpuProbe.lean`)

The M-b spike: probes every SDL_GPU runtime fact the GPU renderer backend
design depends on, before any renderer code exists. Real driver only (SDL_GPU
has no dummy-video backend), so it is not part of the headless suite — run
`lake exe gpu-probe` locally. Kept as a permanent driver-smoke target.

Probed, in order:
1. MSL-source device creation, window claim, swapchain format, present modes.
2. A quad pipeline over instance-rate `[[stage_in]]` attributes with no
   per-vertex buffer (corners from `vertex_id`), shaders released right after
   pipeline creation.
3. `firstInstance` on an instanced draw — instance 0 is a full-target poison
   quad, so a broken base-instance offset turns the readback red.
4. Offscreen color-target render + `downloadFromTexture` pixel asserts (also
   the layer-pass and M-d parity-readback path).
5. The GPU text engine: `gpuDrawData` coordinate convention, winding, image
   type, index well-formedness.
6. Transfer-buffer `cycle` semantics on a mid-frame rewrite, and the
   `waitAndAcquireSwapchainTexture` present loop (resize the window to watch
   live-resize behavior; close it or wait `GPU_PROBE_FRAMES` frames).
7. The whole framework path end-to-end: a `DrawScope.record`ed display list
   (crisp rect, rounded fill, circle, arc mesh, clipped rect, text) rendered
   through `GpuRenderer.renderOffscreen` with pixel asserts.
8. Vector paths (M-e1): band-sweep-tessellated fills (even-odd donut hole,
   non-zero self-intersecting star) through the mesh pipeline.
9. Images (M-f): `ImageBitmap` upload through the process texture cache,
   textured quads on the layer pipeline (nearest scaling, source rects,
   ambient alpha).
10. Graphics-layer transforms (M-g): rotated/scaled layers as mapped
   composite quads (linear sampler), group opacity inside a transformed
   layer, whole-pixel translation snapping, rotated text.
11. Radial/sweep gradients + dithering (M-h): quad-path fragments match the
   `Brush.colorAt` twins on rects (the cases the SDL fallback renders
   coarsely), the sweep seam stays clean, IGN dithering is on for gradient
   fills (and only them — solid quads stay byte-exact).
12. Vertex-buffer-free pipelines + `pushFragmentUniformData` (M-i
   prerequisites, probed standalone before the blur pipeline was wired).
13. Layer blur (M-i): separable Gaussian passes on a line impulse — spread,
   energy conservation, tails, near-identity at tiny σ, group alpha.
14. Fractional-origin text (M-j): a run drawn at a fractional origin is
   byte-identical to the same run drawn at the `snapTextOrigin`-snapped
   integer origin.
15. Cache invalidation: `dropImageTexCache` + `GpuRenderer.invalidateCaches`
   (the backend's `invalidateCaches`) rerenders byte-identically — images
   re-upload and the layer pool/frame buffers regrow lazily.

Exit code is the number of failed checks; informational verdicts (cycle
semantics, y-convention, winding) print as notes for the M-b design.
-/

namespace Demos.GpuProbe

open Sdl.Gpu Compose Compose.Draw

initialize failures : IO.Ref Nat ← IO.mkRef 0

/-- Probe output: stdout, plus SDL's log (→ logcat) on Android, where stdout
goes nowhere — `scripts/smoke-gpu-android.sh`-style wrappers grep the log
for the verdict markers. -/
private def say (msg : String) : IO Unit := do
  IO.println msg
  if (← Sdl.getPlatform) == "Android" then
    Sdl.logInfo (msg := msg)

private def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    say s!"  ok: {name}"
  else
    failures.modify (· + 1)
    say s!"  FAIL: {name}"

private def note (msg : String) : IO Unit := say s!"  {msg}"

/-! ## Little-endian packers (instance data + uniforms) -/

private def pushF32 (b : ByteArray) (f : Float32) : ByteArray :=
  let v := f.toBits
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8
    |>.push (v >>> 24).toUInt8

/-- The 16-byte `Globals` uniform: viewport size + 8 bytes pad. -/
private def globals (w h : Float32) : ByteArray :=
  pushF32 (pushF32 (pushF32 (pushF32 (ByteArray.emptyWithCapacity 16) w) h) 0) 0

/-- One 32-byte quad instance: bounds (x, y, w, h) + non-premultiplied color. -/
private def inst (x y w h r g b a : Float32) : ByteArray := Id.run do
  let mut bs := ByteArray.emptyWithCapacity 32
  for v in [x, y, w, h, r, g, b, a] do
    bs := pushF32 bs v
  return bs

/-- Instance 0 is the poison (drawn only if `firstInstance := 1` is ignored);
instances 1-3 tile three 32×32 quads in a 64×64 world. -/
private def instances : ByteArray :=
  inst 0 0 64 64 1 0 0 1 ++      -- poison: red, full target
  inst 0 0 32 32 0 1 0 1 ++      -- green, top-left
  inst 32 0 32 32 0 0 1 1 ++     -- blue, top-right
  inst 0 32 32 32 1 1 1 1        -- white, bottom-left

/-! ## Shaders

One MSL source, two entry points. Corners come from `vertex_id` over a 4-vertex
triangle strip; all attributes are instance-rate. The `Globals` uniform is
vertex `[[buffer(0)]]` per the SDL binding order; the fragment premultiplies
(the design's blend is `one / oneMinusSrcAlpha`). -/

private def mslSource : String := "
#include <metal_stdlib>
using namespace metal;

struct Globals { float2 viewport; };

struct QuadIn {
  float4 bounds [[attribute(0)]];
  float4 color  [[attribute(1)]];
};

struct VOut {
  float4 pos [[position]];
  float4 color;
};

vertex VOut vmain(QuadIn in [[stage_in]],
                  uint vid [[vertex_id]],
                  constant Globals& g [[buffer(0)]]) {
  float2 corner = float2(float(vid & 1u), float(vid >> 1u));
  float2 p = in.bounds.xy + corner * in.bounds.zw;
  VOut out;
  out.pos = float4(p / g.viewport * float2(2.0, -2.0) + float2(-1.0, 1.0), 0.0, 1.0);
  out.color = in.color;
  return out;
}

fragment float4 fmain(VOut in [[stage_in]]) {
  return float4(in.color.rgb * in.color.a, in.color.a);
}
"

/-- Premultiplied-alpha blending, the design's one blend state. -/
private def premulBlend : ColorTargetBlendState :=
  { srcColorBlendfactor := .one, dstColorBlendfactor := .oneMinusSrcAlpha
    colorBlendOp := .add
    srcAlphaBlendfactor := .one, dstAlphaBlendfactor := .oneMinusSrcAlpha
    alphaBlendOp := .add
    enableBlend := true }

/-- The quad pipeline against a given color-target format (offscreen rgba8 vs
the swapchain's native format). -/
private def makeQuadPipeline (dev : Device) (vs fs : Shader) (target : TextureFormat) :
    IO GraphicsPipeline :=
  dev.createGraphicsPipeline
    { vertexShader := vs
      fragmentShader := fs
      vertexInputState :=
        { vertexBufferDescriptions := #[{ slot := 0, pitch := 32, inputRate := .instance }]
          vertexAttributes :=
            #[{ location := 0, bufferSlot := 0, format := .float4, offset := 0 },
              { location := 1, bufferSlot := 0, format := .float4, offset := 16 }] }
      primitiveType := .triangleStrip
      targetInfo := { colorTargetDescriptions := #[{ format := target, blendState := premulBlend }] } }

/-- RGBA bytes of pixel `(x, y)` in a tightly-packed 64×64 rgba8 readback. -/
private def px (bytes : ByteArray) (x y : Nat) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let o := (y * 64 + x) * 4
  (bytes.get! o, bytes.get! (o + 1), bytes.get! (o + 2), bytes.get! (o + 3))

/-! ## Probe steps -/

/-- ③+④ of the plan's spike list: instanced draw with `firstInstance := 1`
into an offscreen rgba8 target, then `downloadFromTexture` pixel asserts. -/
private def probeOffscreenDraw (dev : Device) (pipe : GraphicsPipeline)
    (ibuf : Buffer) : IO Unit := do
  say "③ firstInstance + offscreen render + readback"
  let tex ← dev.createTexture
    { format := .r8g8b8a8Unorm, usage := .colorTarget, width := 64, height := 64 }
  let dl ← dev.createTransferBuffer .download (64 * 64 * 4)
  let cb ← dev.acquireCommandBuffer
  let rp ← cb.beginRenderPass
    #[{ texture := tex, clearColor := ⟨0, 0, 0, 1⟩, loadOp := .clear }]
  rp.bindPipeline pipe
  rp.bindVertexBuffers 0 #[{ buffer := ibuf }]
  cb.pushVertexUniformData 0 (globals 64 64)
  rp.drawPrimitives 4 (numInstances := 3) (firstVertex := 0) (firstInstance := 1)
  rp.finish
  let cp ← cb.beginCopyPass
  cp.downloadFromTexture { texture := tex, w := 64, h := 64 } { buffer := dl }
  cp.finish
  let fence ← cb.submitAndAcquireFence
  dev.waitForFences true #[fence]
  let bytes ← dl.read
  check "readback size" (bytes.size == 64 * 64 * 4)
  check "instance 1 drawn (green @16,16)" (px bytes 16 16 == (0, 255, 0, 255))
  check "instance 2 drawn (blue @48,16)" (px bytes 48 16 == (0, 0, 255, 255))
  check "instance 3 drawn (white @16,48)" (px bytes 16 48 == (255, 255, 255, 255))
  check "firstInstance honored (poison instance 0 skipped, clear @48,48)"
    (px bytes 48 48 == (0, 0, 0, 255))

/-- ⑤ of the spike list: GPU text engine draw data — the y-axis convention and
winding are the design's biggest unknowns; print everything. Returns the
engine and font for the display-list probe. -/
private def probeTextEngine (dev : Device) (fontPath : String) :
    IO (Sdl.Ttf.TextEngine × Sdl.Ttf.Font) := do
  say "④ GPU text engine + gpuDrawData"
  Sdl.Ttf.init
  let font ← Sdl.Ttf.openFont fontPath 16
  let engine ← Sdl.Ttf.createGpuTextEngine dev
  note s!"engine default winding: {repr (← engine.gpuWinding)}"
  let text ← engine.createText font "Hi jump!"
  let seqs ← text.gpuDrawData
  check "gpuDrawData returns at least one sequence" (seqs.size > 0)
  let mut i := 0
  for s in seqs do
    let nVerts := s.xy.size / 2
    note s!"seq {i}: {nVerts} verts, {s.indices.size} indices, imageType={repr s.imageType}"
    check s!"seq {i}: xy is (x,y) pairs" (s.xy.size % 2 == 0 && s.uv.size == s.xy.size)
    check s!"seq {i}: indices form triangles" (s.indices.size % 3 == 0)
    check s!"seq {i}: indices in range"
      (s.indices.all fun ix => 0 ≤ ix && ix.toNatClampNeg < nVerts)
    if nVerts > 0 then
      let mut minX := s.xy[0]!; let mut maxX := s.xy[0]!
      let mut minY := s.xy[1]!; let mut maxY := s.xy[1]!
      for j in [0:nVerts] do
        minX := min minX (s.xy[2*j]!); maxX := max maxX (s.xy[2*j]!)
        minY := min minY (s.xy[2*j+1]!); maxY := max maxY (s.xy[2*j+1]!)
      note s!"seq {i}: x ∈ [{minX}, {maxX}], y ∈ [{minY}, {maxY}] \
        (negative y ⇒ y-up baseline convention)"
      let mut minU := s.uv[0]!; let mut maxU := s.uv[0]!
      for j in [0:s.uv.size] do
        minU := min minU (s.uv[j]!); maxU := max maxU (s.uv[j]!)
      note s!"seq {i}: uv ∈ [{minU}, {maxU}]"
    if s.indices.size ≥ 3 then
      let at' := fun (k : Nat) => (s.indices[k]!).toNatClampNeg
      let gx := fun (j : Nat) => s.xy[2*j]!
      let gy := fun (j : Nat) => s.xy[2*j+1]!
      let (a, b, c) := (at' 0, at' 1, at' 2)
      let cross := (gx b - gx a) * (gy c - gy a) - (gy b - gy a) * (gx c - gx a)
      note s!"seq {i}: first-triangle cross-z = {cross} \
        (>0 ⇒ CCW in y-up coords = CW on a y-down screen)"
    i := i + 1
  return (engine, font)

/-- ⑥ (first half): does `cycle := true` on a mid-frame transfer-buffer rewrite
preserve the earlier upload? Informational — decides whether M-b may reuse one
transfer buffer within a frame (e.g. for layer passes). -/
private def probeTransferCycle (dev : Device) : IO Unit := do
  say "⑤ transfer-buffer cycle semantics"
  let buf ← dev.createBuffer .vertex 8
  let tb ← dev.createTransferBuffer .upload 4
  let dl ← dev.createTransferBuffer .download 8
  let cb ← dev.acquireCommandBuffer
  tb.write (ByteArray.mk #[0xAA, 0xAA, 0xAA, 0xAA]) (cycle := true)
  let cp ← cb.beginCopyPass
  cp.uploadToBuffer { buffer := tb } { buffer := buf, offset := 0, size := 4 } (cycle := true)
  cp.finish
  tb.write (ByteArray.mk #[0xBB, 0xBB, 0xBB, 0xBB]) (cycle := true)
  let cp2 ← cb.beginCopyPass
  cp2.uploadToBuffer { buffer := tb } { buffer := buf, offset := 4, size := 4 }
  cp2.finish
  let cp3 ← cb.beginCopyPass
  cp3.downloadFromBuffer { buffer := buf, size := 8 } { buffer := dl }
  cp3.finish
  let fence ← cb.submitAndAcquireFence
  dev.waitForFences true #[fence]
  let bytes ← dl.read
  note s!"region 0 = 0x{String.ofList (Nat.toDigits 16 (bytes.get! 0).toNat)}, \
    region 1 = 0x{String.ofList (Nat.toDigits 16 (bytes.get! 4).toNat)} (want AA, BB)"
  if bytes.get! 0 == 0xAA && bytes.get! 4 == 0xBB then
    note "verdict: cycle preserves in-flight writes — one transfer buffer may be reused mid-frame"
  else
    note "verdict: rewrite clobbered the in-flight upload — M-b must write each transfer buffer once per frame"

/-- ⑥ (second half): the vsync present loop over
`waitAndAcquireSwapchainTexture`, submitting on `none`. Resize the window to
observe live-resize behavior; close it to end early. -/
private def probePresentLoop (dev : Device) (window : Sdl.Window)
    (pipe : GraphicsPipeline) (ibuf : Buffer) (frames : Nat) : IO Unit := do
  say s!"⑥ present loop ({frames} frames @ vsync; resize to test, close to end)"
  try dev.setSwapchainParameters window .sdr .vsync
  catch e => note s!"setSwapchainParameters failed: {e}"
  let mut noneCount := 0
  let mut presented := 0
  let mut quit := false
  for _ in [0:frames] do
    if quit then break
    let mut draining := true
    while draining do
      match ← Sdl.pollEvent with
      | none => draining := false
      | some (.quit _) | some (.windowCloseRequested _) => quit := true
      | some _ => pure ()
    let cb ← dev.acquireCommandBuffer
    match ← cb.waitAndAcquireSwapchainTexture window with
    | none =>
      noneCount := noneCount + 1
      cb.submit
    | some sc =>
      let rp ← cb.beginRenderPass
        #[{ texture := sc.texture, clearColor := ⟨0.15, 0.15, 0.15, 1⟩, loadOp := .clear }]
      rp.bindPipeline pipe
      rp.bindVertexBuffers 0 #[{ buffer := ibuf }]
      cb.pushVertexUniformData 0 (globals 64 64)
      rp.drawPrimitives 4 (numInstances := 3) (firstVertex := 0) (firstInstance := 1)
      rp.finish
      cb.submit
      presented := presented + 1
  note s!"presented {presented} frames; waitAndAcquire returned none {noneCount}×"
  check "presented at least one frame" (presented > 0)

/-- ⑯ cache invalidation (the GPU backend's `invalidateCaches`): render an
image + blurred-layer scene, drop the process image-texture cache and the
renderer's pool/buffers, render again — the readback must be byte-identical
(images re-upload and the pool/buffers regrow lazily), proving the reset
path Android's `lowMemory` takes leaves no dangling references behind. -/
private def probeInvalidate (r : Compose.Draw.Gpu.GpuRenderer) : IO Unit := do
  say "⑯ invalidateCaches → lazy re-upload, byte-identical rerender"
  let img ← ImageBitmap.ofPixels 2 2 fun x y =>
    match x, y with
    | 0, 0 => .red
    | 1, 0 => .green
    | 0, 1 => .blue
    | _, _ => .white
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawImage img ⟨10, 10, 50, 50⟩ (sampling := .nearest)
    DrawScope.withLayer ⟨60, 10, 95, 50⟩ 1.0 (effect := .blur 2) do
      DrawScope.drawRect (.solid .white) ⟨70, 20⟩ ⟨20, 20⟩
    DrawScope.drawRect (.solid .red) ⟨100, 10⟩ ⟨30, 20⟩
  let before ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 140 60
  Compose.Draw.Gpu.dropImageTexCache
  r.invalidateCaches
  let after ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 140 60
  check "invalidate: image cache and pool dropped without a hang" true
  check "invalidate: rerender is byte-identical" (before.data == after.data)

/-- ⑥ (SPIR-V-only variant): the same vsync present loop, driven through the
production `GpuRenderer.render` path — the raw-MSL probe pipeline above is
unavailable where the device has no MSL format (Vulkan), and exercising the
real render entry point there is exactly what the Android port needs. -/
private def probePresentLoopRenderer (r : Compose.Draw.Gpu.GpuRenderer)
    (frames : Nat) : IO Unit := do
  say s!"⑥ present loop (production render path; {frames} frames @ vsync; close to end)"
  try r.dev.setSwapchainParameters r.window .sdr .vsync
  catch e => note s!"setSwapchainParameters failed: {e}"
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨30, 20⟩
    DrawScope.drawCircle (.solid .green) ⟨120, 30⟩ 15
  let mut noneCount := 0
  let mut presented := 0
  let mut quit := false
  for _ in [0:frames] do
    if quit then break
    let mut draining := true
    while draining do
      match ← Sdl.pollEvent with
      | none => draining := false
      | some (.quit _) | some (.windowCloseRequested _) => quit := true
      | some _ => pure ()
    if ← r.render ⟨0.15, 0.15, 0.15, 1⟩ list (mayBlock := true) then
      presented := presented + 1
    else
      noneCount := noneCount + 1
  note s!"presented {presented} frames; no swapchain texture {noneCount}×"
  check "presented at least one frame" (presented > 0)

/-- ⑬ (probed *before* the blur pipeline was wired into the renderer, which
depends on both facts): a pipeline with **no vertex buffers at all** (corners
from `vertex_id` only) is accepted, and `pushFragmentUniformData` binds at the
fragment stage's `[[buffer(0)]]` — the codebase's first fragment uniform.
Probing this found a liveness rule instead of an SDL fact: binds don't retain,
so a pipeline local must stay reachable past its draw or Lean's RC frees it
right after `bindPipeline` (SDL debug validation then reads the freed struct
and aborts with a nonsense "missing vertex sampler" assert). -/
private def probeFragmentUniform (dev : Device) : IO Unit := do
  say "⑬ vertex-buffer-free pipeline + pushFragmentUniformData"
  let src := "
#include <metal_stdlib>
using namespace metal;

struct VOut { float4 pos [[position]]; };

vertex VOut uv_vertex(uint vid [[vertex_id]]) {
  float2 corner = float2(float(vid & 1u), float(vid >> 1u));
  VOut out;
  out.pos = float4(corner * 2.0 - 1.0, 0.0, 1.0);
  return out;
}

struct FragColor { float4 color; };

fragment float4 uv_fragment(VOut in [[stage_in]],
                            constant FragColor& c [[buffer(0)]]) {
  return c.color;
}
"
  let vs ← dev.createShader
    { code := src.toUTF8, entrypoint := "uv_vertex", format := .msl, stage := .vertex }
  let fs ← dev.createShader
    { code := src.toUTF8, entrypoint := "uv_fragment", format := .msl, stage := .fragment
      numUniformBuffers := 1 }
  let pipe ← dev.createGraphicsPipeline
    { vertexShader := vs, fragmentShader := fs
      primitiveType := .triangleStrip
      targetInfo := { colorTargetDescriptions := #[{ format := .r8g8b8a8Unorm }] } }
  vs.release
  fs.release
  check "pipeline with zero vertex buffers created" true
  let tex ← dev.createTexture
    { format := .r8g8b8a8Unorm, usage := .colorTarget, width := 8, height := 8 }
  let dl ← dev.createTransferBuffer .download (8 * 8 * 4)
  let cb ← dev.acquireCommandBuffer
  -- The uniform under test: (0.25, 0.5, 0.75, 1) — recognizably non-trivial.
  cb.pushFragmentUniformData 0
    (pushF32 (pushF32 (pushF32 (pushF32 (ByteArray.emptyWithCapacity 16) 0.25) 0.5) 0.75) 1)
  let rp ← cb.beginRenderPass
    #[{ texture := tex, loadOp := .clear, clearColor := ⟨0, 0, 0, 1⟩ }]
  rp.bindPipeline pipe
  rp.drawPrimitives 4 1 0 0
  rp.finish
  let cp ← cb.beginCopyPass
  cp.downloadFromTexture { texture := tex, w := 8, h := 8 } { buffer := dl }
  cp.finish
  let fence ← cb.submitAndAcquireFence
  dev.waitForFences true #[fence]
  let bytes ← dl.read
  -- The explicit releases double as liveness anchors: a bind does NOT retain
  -- (SDL debug validation reads the pipeline struct at draw time), so the
  -- pipeline must stay reachable past the draw — Lean's RC would otherwise
  -- free a dead local right after `bindPipeline`. Found the hard way.
  pipe.release
  tex.release
  dl.release
  let o := (4 * 8 + 4) * 4
  let near := fun (got : UInt8) (want : Nat) =>
    max got.toNat want - min got.toNat want ≤ 1
  check s!"fragment uniform reached [[buffer(0)]] (got {bytes.get! o},{bytes.get! (o+1)},{bytes.get! (o+2)})"
    (near (bytes.get! o) 64 && near (bytes.get! (o+1)) 128 && near (bytes.get! (o+2)) 191)

/-- ⑦ the framework path end-to-end: record a display list with the public
`DrawScope` ops, render it through the real GPU renderer offscreen, and
pixel-assert solid interiors, clipping, and that text marked the target. -/
private def probeDisplayList (r : Compose.Draw.Gpu.GpuRenderer)
    (engine : Sdl.Ttf.TextEngine) (font : Sdl.Ttf.Font)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑦ display list → GPU renderer → offscreen pixels"
  let text ← engine.createText font "Hi"
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨30, 20⟩
    DrawScope.drawRoundRect (.solid .blue) (RoundRect.circular ⟨50, 10, 90, 50⟩ 8)
    DrawScope.drawCircle (.solid .green) ⟨120, 30⟩ 15
    DrawScope.drawArc (.solid .yellow) ⟨120, 70⟩ 12 0 6.28 6
    DrawScope.clipRect ⟨140, 10, 160, 30⟩ do
      DrawScope.drawRect (.solid .white) ⟨140, 10⟩ ⟨40, 40⟩
    DrawScope.drawText { text, string := "Hi", color := .white } ⟨10, 60⟩
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 200 100
  check "offscreen readback size" (bytes.size == 200 * 100 * 4)
  -- Pixel accessor mapping the swapchain format's channel order to (r,g,b,a).
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 200 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  check "crisp rect interior (red @25,20)" (px 25 20 == (255, 0, 0, 255))
  check "rounded fill interior (blue @70,30)" (px 70 30 == (0, 0, 255, 255))
  check "rounded corner clipped (clear @51,11)" (px 51 11 == (0, 0, 0, 255))
  check "circle interior (green @120,30)" (px 120 30 == (0, 255, 0, 255))
  check "arc mesh band (yellow-ish @132,70)" ((px 132 70).1 > 200 && (px 132 70).2.1 > 200)
  check "clip keeps inside (white @150,20)" (px 150 20 == (255, 255, 255, 255))
  check "clip culls below (clear @150,40)" (px 150 40 == (0, 0, 0, 255))
  check "clip culls right (clear @170,20)" (px 170 20 == (0, 0, 0, 255))
  let mut textHits := 0
  for x in [10:40] do
    for y in [60:80] do
      if (px x y).1 > 100 then textHits := textHits + 1
  check s!"text run marked the target ({textHits} lit px in its box)" (textHits > 10)

/-- ⑧ the M-c features end-to-end: real group opacity (no self-overlap
double-blend), the analytic Gaussian shadow, exact rounded clipping of
arbitrary content, and the ripple's masked circle quad. -/
private def probeLayersShadows (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑧ layers, shadows, rounded clip → offscreen pixels"
  let (list, _) ← DrawScope.record {} do
    -- group opacity: two overlapping red rects inside one 50 % layer
    DrawScope.withLayer ⟨10, 10, 90, 50⟩ 0.5 do
      DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨40, 30⟩
      DrawScope.drawRect (.solid .red) ⟨30, 10⟩ ⟨40, 30⟩
    -- a white analytic shadow on the black clear (σ = 4)
    DrawScope.drawShape (.rrShadow (RoundRect.ofRect ⟨110, 10, 150, 50⟩) ⟨0, 0⟩ 8 .white)
    -- rounded clip masks arbitrary content (a crisp rect) exactly
    DrawScope.clipRoundRect (RoundRect.circular ⟨160, 10, 196, 46⟩ 12) do
      DrawScope.drawRect (.solid .green) ⟨160, 10⟩ ⟨36, 36⟩
    -- the bounded ripple: an oversized circle masked by the recorded rrect
    DrawScope.clipRoundRect (RoundRect.circular ⟨10, 60, 46, 96⟩ 12) do
      DrawScope.drawCircle (.solid .yellow) ⟨28, 78⟩ 30
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 220 110
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 220 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  let single := px 15 25    -- covered by the first rect only
  let overlap := px 45 25   -- covered by both rects
  check s!"layer: overlap does not double-blend (single r={single.1}, overlap r={overlap.1})"
    (single == overlap)
  check "layer: composite ≈ 50% red over black"
    (120 ≤ single.1.toNat && single.1.toNat ≤ 136 && single.2.1 == 0)
  check "layer: outside the content is clear" (px 85 45 == (0, 0, 0, 255))
  check s!"shadow: umbra under the shape ≈ full (got {(px 130 30).1})" ((px 130 30).1 > 200)
  let pen := (px 155 30).1.toNat   -- 5 px outside the right edge
  check s!"shadow: penumbra outside the edge (got {pen})" (20 < pen && pen < 220)
  check "shadow: far away clear" (px 210 30 == (0, 0, 0, 255))
  check "rounded clip: interior kept (green @178,28)" (px 178 28 == (0, 255, 0, 255))
  check "rounded clip: corner culled exactly (clear @162,12)" (px 162 12 == (0, 0, 0, 255))
  check "rounded clip: edge midpoint kept (green @178,11)" (px 178 11 == (0, 255, 0, 255))
  check "ripple: interior kept (yellow @28,78)" (px 28 78 == (255, 255, 0, 255))
  check "ripple: rrect corner culled (clear @12,62)" (px 12 62 == (0, 0, 0, 255))
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: one layer, one shadow instance, quads present"
    (stats.layers == 1 && stats.shadows == 1 && stats.quads > 0)

/-- ⑨ vector paths (M-e1): `drawPath` fills lower to band-sweep meshes on the
GPU mesh pipeline — the donut hole and the fill-rule discrimination must
survive the whole encode/replay path. -/
private def probePaths (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑨ path fills → mesh pipeline → offscreen pixels"
  let donut := Path.build (fillRule := .evenOdd) do
    PathM.addOval ⟨10, 10, 70, 70⟩
    PathM.addOval ⟨25, 25, 55, 55⟩
  let star := Path.build (body := do
    let pt (k : Nat) : Offset :=
      let pi : Float := 3.14159265358979323846
      let a := -pi / 2 + k.toFloat * 4 * pi / 5
      ⟨130 + 30 * (Float.cos a).toFloat32, 45 + 30 * (Float.sin a).toFloat32⟩
    PathM.moveTo (pt 0)
    for k in [1:5] do
      PathM.lineTo (pt k)
    PathM.close)
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawPath (.solid .yellow) donut
    DrawScope.drawPath (.solid .red) star
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 180 90
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 180 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  check "donut: ring filled (yellow @40,17)" (px 40 17 == (255, 255, 0, 255))
  check "donut: even-odd hole clear (@40,40)" (px 40 40 == (0, 0, 0, 255))
  check "donut: outside clear (@5,5)" (px 5 5 == (0, 0, 0, 255))
  check "star: non-zero center filled (red @130,45)" (px 130 45 == (255, 0, 0, 255))
  check "star: top arm filled (red @130,25)" (px 130 25 == (255, 0, 0, 255))
  check "star: between arms clear (@130,78)" (px 130 78 == (0, 0, 0, 255))

/-- ⑩ images (M-f): a 2×2 `ImageBitmap` uploads on first use (premultiplied
staging + copy pass) and draws as textured quads on the layer pipeline —
nearest scaling, source-rect cuts, and the ambient alpha fold must survive
the resolve/encode/replay path. -/
private def probeImages (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑩ image upload + textured quads → offscreen pixels"
  let img ← ImageBitmap.ofPixels 2 2 fun x y =>
    match x, y with
    | 0, 0 => .red
    | 1, 0 => .green
    | 0, 1 => .blue
    | _, _ => .white
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawImage img ⟨10, 10, 50, 50⟩ (sampling := .nearest)
    DrawScope.drawImage img ⟨70, 10, 110, 50⟩ (src := some ⟨1, 0, 2, 1⟩)
      (sampling := .nearest)
    DrawScope.withAlpha 0.5 do
      DrawScope.drawImage img ⟨130, 10, 170, 50⟩ (src := some ⟨1, 1, 2, 2⟩)
        (sampling := .nearest)
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 190 60
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 190 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  check "image: quadrant red (@20,20)" (px 20 20 == (255, 0, 0, 255))
  check "image: quadrant green (@40,20)" (px 40 20 == (0, 255, 0, 255))
  check "image: quadrant blue (@20,40)" (px 20 40 == (0, 0, 255, 255))
  check "image: quadrant white (@40,40)" (px 40 40 == (255, 255, 255, 255))
  check "image: src rect all green (@90,30)" (px 90 30 == (0, 255, 0, 255))
  check "image: outside dst clear (@60,30)" (px 60 30 == (0, 0, 0, 255))
  let gray := px 150 30
  check s!"image: ambient alpha folds (got {gray.1})"
    (120 ≤ gray.1.toNat && gray.1.toNat ≤ 136 && gray.1 == gray.2.1)
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: three image quads" (stats.images == 3)

/-- ⑪ graphics-layer transforms (M-g): rotated/scaled layers composite as
mapped textured quads (the linear sampler), group opacity holds inside a
transformed layer, whole-pixel translations snap crisp, and rotated text
survives the layer pass. -/
private def probeTransforms (r : Compose.Draw.Gpu.GpuRenderer)
    (engine : Sdl.Ttf.TextEngine) (font : Sdl.Ttf.Font)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑪ graphics-layer transforms → mapped composites → offscreen pixels"
  let text ← engine.createText font "Hi"
  let (list, _) ← DrawScope.record {} do
    -- 90° rotation about the layer center: left red / right blue → top/bottom
    DrawScope.withGraphicsLayer ⟨10, 10, 50, 50⟩ { rotationZ := 90 } do
      DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨20, 40⟩
      DrawScope.drawRect (.solid .blue) ⟨30, 10⟩ ⟨20, 40⟩
    -- group opacity inside a transformed layer: overlapping red rects at 50 %
    DrawScope.withGraphicsLayer ⟨70, 10, 130, 50⟩ { alpha := 0.5, translationX := 2 } do
      DrawScope.drawRect (.solid .red) ⟨70, 10⟩ ⟨40, 30⟩
      DrawScope.drawRect (.solid .red) ⟨90, 10⟩ ⟨40, 30⟩
    -- whole-pixel translation: snaps to the grid, composites nearest (crisp)
    DrawScope.withGraphicsLayer ⟨140, 10, 160, 30⟩ { translationX := 5, translationY := 3 } do
      DrawScope.drawRect (.solid .white) ⟨140, 10⟩ ⟨20, 20⟩
    -- rotated text: renders axis-aligned into the layer, composite rotates
    DrawScope.withGraphicsLayer ⟨10, 60, 90, 100⟩ { rotationZ := 90 } do
      DrawScope.drawText { text, string := "Hi", color := .white } ⟨15, 70⟩
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 200 120
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 200 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  check "rot90: top half red (@30,15)" (px 30 15 == (255, 0, 0, 255))
  check "rot90: bottom half blue (@30,45)" (px 30 45 == (0, 0, 255, 255))
  check "rot90: outside the layer clear (@55,30)" (px 55 30 == (0, 0, 0, 255))
  let single := px 80 25
  let overlap := px 100 25
  check s!"transformed layer keeps group opacity (single r={single.1}, overlap r={overlap.1})"
    (single == overlap && 120 ≤ single.1.toNat && single.1.toNat ≤ 136)
  check "snap: first covered column crisp (@146,20)" (px 146 20 == (255, 255, 255, 255))
  check "snap: column left of it clear (@143,20)" (px 143 20 == (0, 0, 0, 255))
  -- The run (15..35, 70..86) maps through the 90° rotation about (50,80) to
  -- ≈ (44..60, 45..65) — scan the mapped box, not the recorded one.
  let mut textHits := 0
  for x in [40:65] do
    for y in [40:70] do
      if (px x y).1 > 100 then textHits := textHits + 1
  check s!"rotated text landed in the mapped region ({textHits} lit px)" (textHits > 10)
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: four layers" (stats.layers == 4)

/-- ⑫ radial/sweep gradients + dithering (M-h): the quad fragment's per-kind
`t` must match the `Brush.colorAt`/`Gpu.Sdf` twins on rects — exactly the
shapes whose per-vertex SDL fallback is coarse, so only the GPU can assert
them — and the IGN dither must perturb gradient fills by ±1 step while
leaving solid fills byte-exact. -/
private def probeGradients (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑫ radial/sweep gradient quads + IGN dither → offscreen pixels"
  let radial : Brush := .radial .red .blue ⟨50, 50⟩ 40
  let sweep : Brush := .sweepGradient #[(0, .red), (1, .blue)] ⟨140, 50⟩
  -- A shallow horizontal ramp (16 quantization steps over 180 px — ~11 px
  -- bands without dithering) and a solid quad pinning the dither gate.
  let ramp : Brush := .gradient .black ⟨16.0/255, 16.0/255, 16.0/255, 1⟩ ⟨10, 0⟩ ⟨190, 0⟩
  let solid : Color := ⟨37.0/255, 99.0/255, 201.0/255, 1⟩
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid solid) ⟨2, 2⟩ ⟨6, 6⟩
    DrawScope.drawRect radial ⟨10, 10⟩ ⟨80, 80⟩
    DrawScope.drawRect sweep ⟨100, 10⟩ ⟨80, 80⟩
    DrawScope.drawRect ramp ⟨10, 95⟩ ⟨180, 20⟩
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 200 120
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 200 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  -- Fragment coordinates are pixel centers; ±3/255 covers dither (±0.5),
  -- quantization, and MSL float divergence.
  let checkPx (name : String) (b : Brush) (x y : Nat) : IO Unit := do
    let (er, eg, eb, _) := (b.colorAt ⟨Float32.ofNat x + 0.5, Float32.ofNat y + 0.5⟩).toBytes
    let (gr, gg, gb, _) := px x y
    let d := fun (a b : UInt8) => max a.toNat b.toNat - min a.toNat b.toNat
    check s!"{name} @({x},{y}): got ({gr},{gg},{gb}) want ({er},{eg},{eb})"
      (d gr er ≤ 3 && d gg eg ≤ 3 && d gb eb ≤ 3)
  checkPx "radial: near center" radial 50 50
  checkPx "radial: half radius" radial 70 50
  checkPx "radial: up three-quarters" radial 50 20
  checkPx "radial: diagonal" radial 75 75
  checkPx "radial: corner clamps past the rim" radial 12 12
  checkPx "sweep: t=0.125 (down-right)" sweep 160 70
  checkPx "sweep: t=0.375 (down-left)" sweep 120 70
  checkPx "sweep: t=0.625 (up-left)" sweep 120 30
  checkPx "sweep: t=0.875 (up-right)" sweep 160 30
  -- The seam (+x axis) must be clean: half a pixel above it is almost-wrapped
  -- blue, half a pixel below almost-red — no midway blend.
  checkPx "sweep: just above the seam" sweep 170 49
  checkPx "sweep: just below the seam" sweep 170 50
  -- Dither: neighbor deltas along the ramp stay ≤ 1 (no banding steps get
  -- amplified) …
  let mut maxDelta := 0
  for x in [11:189] do
    let a := (px x 105).1.toNat
    let b := (px (x + 1) 105).1.toNat
    maxDelta := max maxDelta (max a b - min a b)
  check s!"dither: ramp neighbor deltas ≤ 1 (max {maxDelta})" (maxDelta ≤ 1)
  -- … a 16×16 window mean tracks the analytic ramp within ±0.7/255 (banding
  -- alone drifts up to half a step) …
  let mut sum : Float := 0
  let mut analytic : Float := 0
  for x in [40:56] do
    analytic := analytic + ((x.toFloat + 0.5 - 10) / 180 * 16) * 16
    for y in [97:113] do
      sum := sum + (px x y).1.toNat.toFloat
  let drift := (sum - analytic).abs / 256
  check s!"dither: window mean within ±0.7 of analytic (drift {drift})" (drift ≤ 0.7)
  -- … and the dither is actually on: the ramp is constant in y, so without
  -- noise every column would be a single value.
  let mut variedCols := 0
  for x in [30:38] do
    let v0 := (px x 97).1
    let mut varied := false
    for y in [98:113] do
      if (px x y).1 != v0 then varied := true
    if varied then variedCols := variedCols + 1
  check s!"dither: columns vary across rows ({variedCols}/8)" (variedCols ≥ 6)
  -- Solid fills bypass the dither gate — byte-exact.
  check "solid quad stays byte-exact (@5,5)" (px 5 5 == (37, 99, 201, 255))
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: all four fills took the quad path"
    (stats.quads == 4 && stats.meshTriangles == 0)

/-- ⑭ layer blur (M-i) end-to-end: `withBlur` content renders into a pooled
texture, bounces through the separable H/V Gaussian passes, and composites.
A 1 px white line under σ = 4 is a clean impulse response — the discrete
normalized kernel puts `255/wsum ≈ 25` at the peak, `≈ 15` at ±σ, `≈ 3` at
±2σ, nothing at ±4σ, and preserves the column integral (`≈ 255`). σ = 0.5
must be a near-identity on solid interiors (the kernel normalizes), and blur
composes with group alpha and spreads past the recorded bounds (the `3σ + 1`
margin). -/
private def probeBlur (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑭ layer blur → separable Gaussian passes → offscreen pixels"
  let (list, _) ← DrawScope.record {} do
    -- impulse: a 1 px white line, σ = 4
    DrawScope.withBlur ⟨10, 10, 90, 70⟩ 4 do
      DrawScope.drawRect (.solid .white) ⟨10, 40⟩ ⟨80, 1⟩
    -- near-identity: a solid block, σ = 0.5
    DrawScope.withBlur ⟨100, 10, 160, 70⟩ 0.5 do
      DrawScope.drawRect (.solid .white) ⟨100, 20⟩ ⟨40, 30⟩
    -- blur composes with group alpha; tails spread past the recorded bounds
    DrawScope.withLayer ⟨170, 30, 190, 50⟩ 0.5 (effect := .blur 3) do
      DrawScope.drawRect (.solid .white) ⟨170, 30⟩ ⟨20, 20⟩
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 200 90
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 200 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  let v := fun (x y : Nat) => (px x y).1.toNat
  check s!"impulse: peak ≈ 25 (got {v 50 40})" (18 ≤ v 50 40 && v 50 40 ≤ 33)
  check s!"impulse: ±σ ≈ 15 (got {v 50 36}/{v 50 44})"
    (12 ≤ v 50 36 && v 50 36 ≤ 22 && 12 ≤ v 50 44 && v 50 44 ≤ 22)
  check s!"impulse: ±2σ ≈ 3 (got {v 50 32}/{v 50 48})"
    (1 ≤ v 50 32 && v 50 32 ≤ 8 && 1 ≤ v 50 48 && v 50 48 ≤ 8)
  check s!"impulse: ±4σ gone (got {v 50 24}/{v 50 56})" (v 50 24 ≤ 1 && v 50 56 ≤ 1)
  let mut energy := 0
  for y in [24:57] do
    energy := energy + v 50 y
  check s!"impulse: column energy preserved within 10% (got {energy})"
    (229 ≤ energy && energy ≤ 281)
  check s!"σ=0.5: interior is identity (got {v 120 35})" (v 120 35 ≥ 253)
  check s!"σ=0.5: 4 px outside stays dark (got {v 120 54})" (v 120 54 ≤ 2)
  check s!"blur × alpha 0.5: block center ≈ 127 (got {v 180 40})"
    (110 ≤ v 180 40 && v 180 40 ≤ 142)
  check s!"blur spreads past the recorded bounds (got {v 194 40} @ 4 px out)"
    (v 194 40 ≥ 5 && v 194 40 ≤ 40)
  check "background untouched" (px 5 5 == (0, 0, 0, 255))
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: three layers" (stats.layers == 3)

/-- ⑮ fractional-origin text (M-j): both backends snap run origins through
the shared `snapTextOrigin`, so drawing at ⟨10.4, 60.6⟩ must produce the
byte-identical frame to drawing at the snapped ⟨10, 61⟩. -/
private def probeFractionalText (r : Compose.Draw.Gpu.GpuRenderer)
    (engine : Sdl.Ttf.TextEngine) (font : Sdl.Ttf.Font) : IO Unit := do
  say "⑮ fractional text origin snaps to the integer rendering"
  let text ← engine.createText font "Hi jump!"
  let render (origin : Offset) : IO ByteArray := do
    let (list, _) ← DrawScope.record {} do
      DrawScope.drawText { text, string := "Hi jump!", color := .white } origin
    r.renderOffscreen ⟨0, 0, 0, 1⟩ list 120 90
  let frac ← render ⟨10.4, 60.6⟩
  let snapped ← render ⟨10, 61⟩
  check "snapTextOrigin pins the probe's origins"
    (snapTextOrigin ⟨10.4, 60.6⟩ .zero == (⟨10, 61⟩ : Offset))
  let mut lit := 0
  for i in [0:frac.size] do
    -- color bytes only (alpha is last in both rgba8/bgra8 swapchain orders,
    -- and is 255 everywhere on the opaque clear)
    if i % 4 != 3 && frac.get! i > 100 then lit := lit + 1
  check s!"fractional draw marked the target ({lit} lit color bytes)" (lit > 40)
  check "fractional origin renders byte-identical to the snapped origin"
    (frac.data == snapped.data)

def run (fontPath : String := "assets/fonts/Roboto-Regular.ttf")
    (frames? : Option Nat := none) : IO UInt32 := do
  let frames := frames?.getD (((← IO.getEnv "GPU_PROBE_FRAMES").bind (·.toNat?)).getD 180)
  say "== gpu-probe: SDL_GPU runtime facts for the GPU renderer backend =="
  Sdl.init .video

  say "① device + swapchain"
  note s!"built-in GPU drivers: {← getDrivers}"
  let driver ← IO.getEnv "COMPOSE_GPU_DRIVER"
  check "MSL or SPIR-V shader format supported"
    (← supportsShaderFormats (ShaderFormat.msl ||| .spirv) driver)
  let dev ← createDevice (ShaderFormat.msl ||| .spirv) (debugMode := true) (name := driver)
  note s!"device driver: {← dev.getDriver}"
  let formats ← dev.getShaderFormats
  note s!"device shader formats: {formats.val}"
  let hasMsl := formats.has .msl
  -- Same flags as compose-ui's bootstrapWindow — the probe must exercise
  -- the exact window configuration the framework renders into.
  let window ← Sdl.createWindow "gpu-probe" 512 384
    (Sdl.WindowFlags.resizable ||| .highPixelDensity)
  dev.claimWindow window
  let swapchainFmt ← dev.getSwapchainTextureFormat window
  note s!"swapchain format: {repr swapchainFmt}"
  check "swapchain is an 8-bit UNORM format"
    (swapchainFmt == .b8g8r8a8Unorm || swapchainFmt == .r8g8b8a8Unorm)
  dev.setAllowedFramesInFlight 2
  for mode in [PresentMode.vsync, .immediate, .mailbox] do
    note s!"present mode {repr mode} supported: {← dev.windowSupportsPresentMode window mode}"

  -- The raw-MSL micro-probes (②③⑬ and the raw present loop) need MSL-source
  -- support (Metal). On SPIR-V-only devices (Vulkan) the same SDL facts are
  -- exercised through the framework pipelines (⑦–⑮ build all six from the
  -- embedded SPIR-V blobs), and the present loop runs on the production
  -- render path instead.
  let raw ← if hasMsl then do
      say "② MSL shader pair + instance-rate quad pipelines"
      let vs ← dev.createShader
        { code := mslSource.toUTF8, entrypoint := "vmain", format := .msl, stage := .vertex
          numUniformBuffers := 1 }
      let fs ← dev.createShader
        { code := mslSource.toUTF8, entrypoint := "fmain", format := .msl, stage := .fragment }
      let offscreenPipe ← makeQuadPipeline dev vs fs .r8g8b8a8Unorm
      let windowPipe ← makeQuadPipeline dev vs fs swapchainFmt
      vs.release
      fs.release
      check "MSL source compiled; pipelines created; shaders released after" true

      let ibuf ← dev.createBuffer .vertex (UInt32.ofNat instances.size)
      let up ← dev.createTransferBuffer .upload (UInt32.ofNat instances.size)
      let cb ← dev.acquireCommandBuffer
      up.write instances (cycle := true)
      let cp ← cb.beginCopyPass
      cp.uploadToBuffer { buffer := up }
        { buffer := ibuf, size := UInt32.ofNat instances.size } (cycle := true)
      cp.finish
      cb.submit
      pure (some (offscreenPipe, windowPipe, ibuf))
    else do
      say "② raw-MSL micro-probes skipped (device has no MSL format)"
      pure none

  if let some (offscreenPipe, _, ibuf) := raw then
    probeOffscreenDraw dev offscreenPipe ibuf
  let (engine, font) ← probeTextEngine dev fontPath
  probeTransferCycle dev
  let gpuRenderer ← Compose.Draw.Gpu.GpuRenderer.create dev window
  probeDisplayList gpuRenderer engine font swapchainFmt
  probeLayersShadows gpuRenderer swapchainFmt
  probePaths gpuRenderer swapchainFmt
  probeImages gpuRenderer swapchainFmt
  probeTransforms gpuRenderer engine font swapchainFmt
  probeGradients gpuRenderer swapchainFmt
  if hasMsl then
    probeFragmentUniform dev
  else
    note "⑬ raw-MSL fragment-uniform micro-probe skipped (the blur pipeline covers pushFragmentUniformData on SPIR-V)"
  probeBlur gpuRenderer swapchainFmt
  probeFractionalText gpuRenderer engine font
  probeInvalidate gpuRenderer
  match raw with
  | some (_, windowPipe, ibuf) => probePresentLoop dev window windowPipe ibuf frames
  | none => probePresentLoopRenderer gpuRenderer frames

  dev.releaseWindow window
  let n ← failures.get
  say (if n == 0 then "== gpu-probe: all checks passed ==" else s!"== gpu-probe: {n} FAILED ==")
  return UInt32.ofNat n

end Demos.GpuProbe
