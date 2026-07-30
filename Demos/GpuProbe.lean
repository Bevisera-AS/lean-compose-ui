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

/-- ⑰ the overscroll stretch warp (M-i2): stripes recorded in `.stretch`
layers must land where the `Gpu.Sdf.stretchPos` twin predicts — the pinned
edge stays put, interior content magnifies away from the pin, content past
the visible `1/(1+s)` source window vanishes, the mirror sign pins the far
edge, the horizontal axis warps independently, and the composite still
scales by group alpha. Exercises the stretch pipeline's mid-pass
`pushFragmentUniformData` on every driver. -/
private def probeStretch (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑰ layer stretch → warped composite → offscreen pixels"
  let (list, _) ← DrawScope.record {} do
    -- A: vertical s = 0.5, pin at the top of a 100×100 layer; stripes at
    -- source rows 10, 55, 100 (the last is past the 1/1.5 source window).
    DrawScope.withGraphicsLayer ⟨20, 10, 120, 110⟩ {}
      (do
        DrawScope.drawRect (.solid .white) ⟨20, 10⟩ ⟨100, 4⟩
        DrawScope.drawRect (.solid .white) ⟨20, 55⟩ ⟨100, 4⟩
        DrawScope.drawRect (.solid .white) ⟨20, 100⟩ ⟨100, 4⟩)
      (effect := .stretch 0 0.5)
    -- B: the mirror (s = −0.5) pins the bottom; the top stripe vanishes.
    DrawScope.withGraphicsLayer ⟨20, 130, 120, 230⟩ {}
      (do
        DrawScope.drawRect (.solid .white) ⟨20, 130⟩ ⟨100, 4⟩
        DrawScope.drawRect (.solid .white) ⟨20, 226⟩ ⟨100, 4⟩)
      (effect := .stretch 0 (-0.5))
    -- C: the horizontal axis, pin at the left of a 60×60 layer.
    DrawScope.withGraphicsLayer ⟨130, 10, 190, 70⟩ {}
      (do
        DrawScope.drawRect (.solid .white) ⟨130, 10⟩ ⟨4, 60⟩
        DrawScope.drawRect (.solid .white) ⟨160, 10⟩ ⟨4, 60⟩)
      (effect := .stretch 0.5 0)
    -- D: stretch composes with group alpha (a solid white fill at 50%).
    DrawScope.withLayer ⟨130, 130, 170, 170⟩ 0.5
      (DrawScope.drawRect (.solid .white) ⟨130, 130⟩ ⟨40, 40⟩)
      (effect := .stretch 0 0.3)
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 210 240
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (x y : Nat) =>
    let o := (y * 210 + x) * 4
    if bgra then (bytes.get! (o+2), bytes.get! (o+1), bytes.get! o, bytes.get! (o+3))
    else (bytes.get! o, bytes.get! (o+1), bytes.get! (o+2), bytes.get! (o+3))
  -- Predicted output coordinate (target px) where content recorded at source
  -- coordinate `src` appears: the layer's margin-inflated bounds start at
  -- `origin` with `extent` px on the stretched axis; invert the
  -- `Gpu.Sdf.stretchPos` twin by scanning at 0.1 px resolution.
  let predict := fun (origin extent src s : Float32) => Id.run do
    let mut best := origin
    let mut bestD : Float32 := 1e9
    for i in [0:(extent * 10).toUInt32.toNat + 1] do
      let y := origin + Float32.ofNat i / 10
      let sy := origin + extent * Compose.Draw.Gpu.stretchPos ((y - origin) / extent) s
      if (sy - src).abs < bestD then
        bestD := (sy - src).abs
        best := y
    return best
  -- Maximal runs of lit indices in [n0, n1).
  let bands := fun (n0 n1 : Nat) (lit : Nat → Bool) => Id.run do
    let mut out : Array (Nat × Nat) := #[]
    let mut cur : Option Nat := none
    for i in [n0:n1] do
      if lit i then
        if cur.isNone then cur := some i
      else if let some s0 := cur then
        out := out.push (s0, i - 1)
        cur := none
    if let some s0 := cur then out := out.push (s0, n1 - 1)
    return out
  let near := fun (mid : Float32) (band : Nat × Nat) =>
    decide (((Float32.ofNat (band.1 + band.2) / 2) - mid).abs < 2.5)
  -- A (LayerEnc bounds start 9, extent 102 after the 1 px margin):
  let a := bands 9 118 (fun y => (px 70 y).1.toNat > 100)
  check s!"stretch: two of three stripes visible ({a})" (a.size == 2)
  if a.size == 2 then
    check s!"stretch: pinned-edge stripe stays at the pin ({(a[0]!).1})"
      (9 ≤ (a[0]!).1 && (a[0]!).1 ≤ 13)
    check s!"stretch: interior stripe lands where the twin predicts ({a[1]!} vs {predict 9 102 57 0.5})"
      (near (predict 9 102 57 0.5) a[1]!)
  -- B mirror (bounds start 129, extent 102, pin at the bottom):
  let b := bands 129 235 (fun y => (px 70 y).1.toNat > 100)
  check s!"stretch mirror: only the pinned-edge stripe survives ({b})" (b.size == 1)
  if b.size == 1 then
    check s!"stretch mirror: it lands where the twin predicts, hugging the pin ({b[0]!} vs {predict 129 102 228 (-0.5)})"
      (near (predict 129 102 228 (-0.5)) b[0]! && 226 ≤ (b[0]!).2 && (b[0]!).2 ≤ 231)
  -- C horizontal (bounds start 129, extent 62):
  let c := bands 129 194 (fun x => (px x 40).1.toNat > 100)
  check s!"stretch x-axis: both stripes visible ({c})" (c.size == 2)
  if c.size == 2 then
    check s!"stretch x-axis: pinned-edge stripe stays ({(c[0]!).1})"
      (129 ≤ (c[0]!).1 && (c[0]!).1 ≤ 133)
    check s!"stretch x-axis: interior stripe lands where the twin predicts ({c[1]!} vs {predict 129 62 162 0.5})"
      (near (predict 129 62 162 0.5) c[1]!)
  -- D: group alpha still scales the warped composite.
  let d := (px 150 150).1.toNat
  check s!"stretch × alpha 0.5: center ≈ 127 (got {d})" (110 ≤ d && d ≤ 142)
  check "background untouched" (px 5 5 == (0, 0, 0, 255))
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: four layers" (stats.layers == 4)

/-- ⑱ rounded-clipped layer composites (Wave 2b): a rounded clip enclosing
an offscreen layer rides the `LayerEnc` and masks the composite in the layer
fragment (`LayerClip` uniform) — a blurred layer's corner is culled exactly
where the quad SDF says while its interior and edge midpoints keep the
blurred content; a translucent layer culls the same way; and an unmasked
layer drawn *after* masked ones in the same pass gets the sentinel re-pushed
(the `pushedClip` tracker), rendering byte-identical to the same layer
alone. -/
private def probeLayerClip (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑱ rounded-clipped layer composites → masked pixels"
  let unmasked : Draw.DrawM Unit :=
    DrawScope.withLayer ⟨170, 10, 190, 30⟩ 0.5 do
      DrawScope.drawRect (.solid .white) ⟨170, 10⟩ ⟨20, 20⟩
  let (list, _) ← DrawScope.record {} do
    -- A: blurred layer under a rounded clip — the blur must not leak past
    -- the rounded corner.
    DrawScope.clipRoundRect (RoundRect.circular ⟨10, 10, 70, 70⟩ 12) do
      DrawScope.withBlur ⟨10, 10, 70, 70⟩ 4 do
        DrawScope.drawRect (.solid .white) ⟨10, 10⟩ ⟨60, 60⟩
    -- B: translucent layer under a rounded clip.
    DrawScope.clipRoundRect (RoundRect.circular ⟨100, 10, 160, 70⟩ 16) do
      DrawScope.withLayer ⟨100, 10, 160, 70⟩ 0.5 do
        DrawScope.drawRect (.solid .red) ⟨100, 10⟩ ⟨60, 60⟩
    -- C: an unmasked layer after the masked ones (sentinel restoration).
    unmasked
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 200 100
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (bs : ByteArray) (x y : Nat) =>
    let o := (y * 200 + x) * 4
    if bgra then (bs.get! (o+2), bs.get! (o+1), bs.get! o, bs.get! (o+3))
    else (bs.get! o, bs.get! (o+1), bs.get! (o+2), bs.get! (o+3))
  let v := fun (x y : Nat) => (px bytes x y).1.toNat
  check s!"blur: rounded corner culled (got {v 12 12} @12,12)" (v 12 12 == 0)
  check s!"blur: interior keeps the blurred content (got {v 40 40})" (v 40 40 ≥ 250)
  check s!"blur: edge midpoint keeps the blurred falloff (got {v 40 11})"
    (120 ≤ v 40 11 && v 40 11 ≤ 210)
  check "blur: outside the clip untouched" (px bytes 5 5 == (0, 0, 0, 255))
  check s!"alpha: rounded corner culled (got {v 103 13} @103,13)" (v 103 13 == 0)
  check s!"alpha: center composites at 50% (got {(px bytes 130 40).1})"
    (110 ≤ v 130 40 && v 130 40 ≤ 142)
  check s!"alpha: edge midpoint kept (got {v 130 11})" (110 ≤ v 130 11 && v 130 11 ≤ 142)
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: three layers" (stats.layers == 3)
  -- The unmasked layer after masked draws must match the same layer alone.
  let (alone, _) ← DrawScope.record {} unmasked
  let ref ← r.renderOffscreen ⟨0, 0, 0, 1⟩ alone 200 100
  let mut regionSame := true
  for x in [168:192] do
    for y in [8:32] do
      if px bytes x y != px ref x y then regionSame := false
  check "sentinel: unmasked layer after masked ones is byte-identical to the layer alone"
    regionSame

/-- ⑲ true backdrop blur (Wave 3): a `drawBackdrop` panel splits the frame —
the prefix renders into the snapshot, the panel's region blurs at a
downsampled resolution, and the composite draws it masked by the rounded
clip. Over a red/blue seam base: outside the panel the 1:1 blit keeps the
base byte-exact, the culled rounded corner shows the *crisp* base (a white
marker square), constant regions survive the downsample→blur→upsample chain
(≈ identity), the seam frosts to a monotonic red↔blue ramp, and text/image
prims on both sides of the split keep the resolve/encode walks in lockstep
(the suffix draws crisp, on top). A second scene runs σ = 40 — the
two-halving path — where a small white marker must dilute to ≈ the
background (the blur really ran at quarter resolution). -/
private def probeBackdrop (r : Compose.Draw.Gpu.GpuRenderer)
    (engine : Sdl.Ttf.TextEngine) (font : Sdl.Ttf.Font)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑲ backdrop panels → snapshot split + region blurs → offscreen pixels"
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (bs : ByteArray) (w x y : Nat) =>
    let o := (y * w + x) * 4
    if bgra then (bs.get! (o+2), bs.get! (o+1), bs.get! o, bs.get! (o+3))
    else (bs.get! o, bs.get! (o+1), bs.get! (o+2), bs.get! (o+3))
  -- Scene 1: red|blue seam at x = 100, a white 6×6 marker on the panel's
  -- rounded corner, text + image prims before AND after the backdrop.
  let img ← ImageBitmap.ofPixels 2 2 fun x y =>
    match x, y with
    | 0, 0 => .red
    | 1, 0 => .green
    | 0, 1 => .blue
    | _, _ => .white
  let preText ← engine.createText font "Hi"
  let postText ← engine.createText font "Hi"
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .red) ⟨0, 0⟩ ⟨100, 140⟩
    DrawScope.drawRect (.solid .blue) ⟨100, 0⟩ ⟨120, 140⟩
    DrawScope.drawRect (.solid .white) ⟨40, 20⟩ ⟨6, 6⟩
    DrawScope.drawText { text := preText, string := "Hi", color := .white } ⟨10, 110⟩
    DrawScope.drawImage img ⟨190, 105, 214, 129⟩ (sampling := .nearest)
    DrawScope.clipRoundRect (RoundRect.circular ⟨40, 20, 120, 100⟩ 16) do
      DrawScope.drawBackdrop ⟨40, 20, 120, 100⟩ 8
    DrawScope.drawText { text := postText, string := "Hi", color := .black } ⟨70, 55⟩
    DrawScope.drawImage img ⟨130, 105, 154, 129⟩ (sampling := .nearest)
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 220 140
  let p := px bytes 220
  check "blit: outside the panel the base is byte-exact (red @20,60)"
    (p 20 60 == (255, 0, 0, 255))
  check "blit: and on the blue side (@200,60)" (p 200 60 == (0, 0, 255, 255))
  check s!"mask: rounded corner culled — the marker stays crisp white (got {p 43 23})"
    ((p 43 23).1 ≥ 250 && (p 43 23).2.1 ≥ 250 && (p 43 23).2.2.1 ≥ 250)
  check s!"frost: just inside the mask the marker smears (g = {(p 48 26).2.1})"
    (4 ≤ (p 48 26).2.1.toNat && (p 48 26).2.1.toNat ≤ 100)
  check s!"frost: constant region ≈ identity through the chain (got {p 55 88})"
    ((p 55 88).1.toNat ≥ 245 && (p 55 88).2.1.toNat ≤ 8 && (p 55 88).2.2.1.toNat ≤ 8)
  let seam := p 100 90
  check s!"frost: seam center is the red/blue mix (r={seam.1} b={seam.2.2.1})"
    (90 ≤ seam.1.toNat && seam.1.toNat ≤ 170
      && 85 ≤ seam.2.2.1.toNat && seam.2.2.1.toNat ≤ 170)
  check s!"frost: monotonic ramp across the seam ({(p 88 90).1} > {seam.1} > {(p 112 90).1})"
    ((p 88 90).1 > seam.1 && seam.1 > (p 112 90).1
      && (p 88 90).1.toNat ≥ 175 && (p 112 90).1.toNat ≤ 80)
  let mut preLit := 0
  for x in [10:40] do
    for y in [110:130] do
      if (p x y).2.1 > 100 then preLit := preLit + 1
  check s!"lockstep: prefix text blitted through the snapshot ({preLit} lit px)" (preLit > 10)
  let mut postDark := 0
  for x in [70:100] do
    for y in [55:75] do
      if (p x y).1 < 120 then postDark := postDark + 1
  check s!"lockstep: suffix text drew crisp over the frost ({postDark} dark px)" (postDark > 10)
  check "lockstep: prefix image quadrant (red @196,111)" (p 196 111 == (255, 0, 0, 255))
  check "lockstep: prefix image quadrant (white @208,123)" (p 208 123 == (255, 255, 255, 255))
  check "lockstep: suffix image quadrant (red @136,111)" (p 136 111 == (255, 0, 0, 255))
  check "lockstep: suffix image quadrant (white @148,123)" (p 148 123 == (255, 255, 255, 255))
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: one backdrop, two images, snapshot in the pool"
    (stats.backdrops == 1 && stats.images == 2 && stats.poolTextures ≥ 3)
  -- Scene 2: σ = 40 (the two-halving path) over a mid-gray base — a 10×10
  -- white marker under the panel must dilute to ≈ the background (its whole
  -- mass spreads over (3σ)²), while a marker outside the panel stays crisp.
  let (list2, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .white) ⟨105, 65⟩ ⟨10, 10⟩
    DrawScope.drawRect (.solid .white) ⟨10, 10⟩ ⟨10, 10⟩
    DrawScope.clipRoundRect (RoundRect.circular ⟨40, 20, 180, 120⟩ 8) do
      DrawScope.drawBackdrop ⟨40, 20, 180, 120⟩ 40
  let bytes2 ← r.renderOffscreen ⟨0.5, 0.5, 0.5, 1⟩ list2 220 140
  let q := px bytes2 220
  check s!"σ=40: the marker dilutes into the frost (got {(q 110 70).1})"
    (110 ≤ (q 110 70).1.toNat && (q 110 70).1.toNat ≤ 150)
  check s!"σ=40: constant gray survives the two-halving chain (got {(q 60 90).1})"
    (((((q 60 90).1.toNat : Int)) - 128).natAbs ≤ 8)
  check "σ=40: marker outside the panel stays crisp white via the blit"
    (q 15 15 == (255, 255, 255, 255))
  let stats2 ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats2.brief}"
  check "frame stats: the σ=40 panel is one backdrop" (stats2.backdrops == 1)

/-- ⑳ refractive glass composite (Wave 4): a backdrop panel whose
`Refraction` is on routes through the **glass** pipeline — sample positions
displace outward along the panel SDF's gradient near the rim
(`strength · (1 − smoothstep 0 band depth)`, twins `Gpu.Sdf.rrectGrad` /
`refractShift`), pulling backdrop content inward like a lens. Over a
red|blue seam 5 px inside the panel's right edge (σ = 1 keeps the frost
sharp enough to localize the bend): a midline pixel in the bend band
samples from *beyond* the seam (blue where the unwarped frost is red), the
bend stays confined to the band (15 px further in the frost is still local
red), the deep interior is identity, and the culled rounded corner plus
everything outside the panel stay byte-exact base. A second scene sets
`chroma` over a black|white seam — the red channel samples further along
the outward gradient than the blue one, so a mid-ramp pixel splits warm. -/
private def probeRefraction (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "⑳ refracting backdrop panels → glass pipeline pixels"
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (bs : ByteArray) (w x y : Nat) =>
    let o := (y * w + x) * 4
    if bgra then (bs.get! (o+2), bs.get! (o+1), bs.get! o, bs.get! (o+3))
    else (bs.get! o, bs.get! (o+1), bs.get! (o+2), bs.get! (o+3))
  let refr : Draw.Refraction := { strength := 12, band := 16 }
  -- Scene 1: red|blue seam at x = 155, panel right rim at x = 160.
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .red) ⟨0, 0⟩ ⟨155, 140⟩
    DrawScope.drawRect (.solid .blue) ⟨155, 0⟩ ⟨65, 140⟩
    DrawScope.clipRoundRect (RoundRect.circular ⟨60, 20, 160, 100⟩ 12) do
      DrawScope.drawBackdrop ⟨60, 20, 160, 100⟩ 1 refr
  let bytes ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list 220 140
  let p := px bytes 220
  check "blit: outside the panel stays byte-exact (red @30,60)"
    (p 30 60 == (255, 0, 0, 255))
  check "blit: and past the panel on the blue side (@200,60)"
    (p 200 60 == (0, 0, 255, 255))
  check "blit: between rim and window edge (@170,60)" (p 170 60 == (0, 0, 255, 255))
  check "mask: the glass pipeline culls the rounded corner to the crisp base (@62,22)"
    (p 62 22 == (255, 0, 0, 255))
  let deep := p 110 60
  check s!"identity: deep interior (past the band) is the local red (r={deep.1})"
    (deep.1.toNat ≥ 250 && deep.2.2.1.toNat ≤ 5)
  -- Frag (153.5, 60.5): depth 6.5 ⟹ shift 12·0.639 ≈ 7.7 px outward — the
  -- sample lands ≈ 6 px past the seam, on pure blue (Gpu.Sdf.refractShift's
  -- pinned operating point).
  let bent := p 153 60
  check s!"bend: in the rim band the sample crosses the seam (r={bent.1} b={bent.2.2.1})"
    (bent.2.2.1.toNat ≥ 200 && bent.1.toNat ≤ 60)
  -- Frag (145.5, 60.5): depth 14.5 ⟹ shift ≈ 0.3 px — still local red.
  let confined := p 145 60
  check s!"bend: confined to the band — 15 px inside is still red (r={confined.1})"
    (confined.1.toNat ≥ 240 && confined.2.2.1.toNat ≤ 15)
  let leftRim := p 66 60
  check s!"bend: the far rim pulls only local red (r={leftRim.1})" (leftRim.1.toNat ≥ 240)
  let stats ← Compose.Draw.Gpu.frameStats.get
  note s!"frame stats: {stats.brief}"
  check "frame stats: one refracting backdrop" (stats.backdrops == 1)
  -- Scene 2: chroma over a black|white seam. Frag (151.5, 60.5): depth 8.5
  -- ⟹ falloff 0.453, bend ≈ 5.4 px, split ±3·0.453 ≈ ±1.4 px — the red
  -- sample lands on pure white, the blue one back on the ramp.
  let (list2, _) ← DrawScope.record {} do
    DrawScope.drawRect (.solid .black) ⟨0, 0⟩ ⟨155, 140⟩
    DrawScope.drawRect (.solid .white) ⟨155, 0⟩ ⟨65, 140⟩
    DrawScope.clipRoundRect (RoundRect.circular ⟨60, 20, 160, 100⟩ 12) do
      DrawScope.drawBackdrop ⟨60, 20, 160, 100⟩ 1 { refr with chroma := 3 }
  let bytes2 ← r.renderOffscreen ⟨0, 0, 0, 1⟩ list2 220 140
  let q := px bytes2 220
  let split := q 151 60
  check s!"chroma: a mid-ramp pixel splits warm (r={split.1} b={split.2.2.1})"
    (split.1.toNat ≥ split.2.2.1.toNat + 30)
  check "chroma: outside the panel stays neutral white"
    (q 200 60 == (255, 255, 255, 255))

/-- ㉑ squircle (continuous) corners: `cornerStyle` rides the quad
instance's pad float and flips the fragment SDF to `squircle_sdf` — for a
white rect ⟨10,10,90,90⟩ r 16 the diagonal **bulge** pixel (13,13) lies
inside the superellipse (4-norm 14.9 < 16) but outside the circle
(Euclidean 17.7 > 16), so it fills for `.continuous` and stays background
for `.circular`; further out (11,11) is beyond both; edge midpoints match
byte-exactly; and a `.continuous` *stroke* passes through the diagonal
boundary pixel (12,12) that the circular stroke leaves empty. -/
private def probeSquircle (r : Compose.Draw.Gpu.GpuRenderer)
    (swapchainFmt : Sdl.Gpu.TextureFormat) : IO Unit := do
  say "㉑ squircle corners → 4-norm SDF pixels"
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let px := fun (bs : ByteArray) (x y : Nat) =>
    let o := (y * 100 + x) * 4
    if bgra then (bs.get! (o+2), bs.get! (o+1), bs.get! o, bs.get! (o+3))
    else (bs.get! o, bs.get! (o+1), bs.get! (o+2), bs.get! (o+3))
  let rr := RoundRect.circular ⟨10, 10, 90, 90⟩ 16
  let render (corners : Draw.CornerStyle) (style : Draw.DrawStyle) : IO ByteArray := do
    let (list, _) ← DrawScope.record {} do
      DrawScope.drawRoundRect (.solid .white) rr style corners
    r.renderOffscreen ⟨0, 0, 0, 1⟩ list 100 100
  let sq ← render .continuous .fill
  let ci ← render .circular .fill
  check s!"fill: the corner bulge pixel fills for continuous (got {(px sq 13 13).1})"
    ((px sq 13 13).1.toNat ≥ 250)
  check s!"fill: … and stays background for circular (got {(px ci 13 13).1})"
    ((px ci 13 13).1.toNat ≤ 5)
  check "fill: beyond the superellipse both are background"
    ((px sq 11 11).1.toNat ≤ 5 && (px ci 11 11).1.toNat ≤ 5)
  check "fill: edge midpoints are byte-identical across styles"
    (px sq 50 11 == px ci 50 11 && px sq 10 50 == px ci 10 50
      && px sq 50 50 == px ci 50 50)
  let sqs ← render .continuous (.stroke 3)
  let cis ← render .circular (.stroke 3)
  check s!"stroke: the squircle band passes the diagonal boundary pixel (got {(px sqs 12 12).1})"
    ((px sqs 12 12).1.toNat ≥ 250)
  check s!"stroke: … which the circular band leaves empty (got {(px cis 12 12).1})"
    ((px cis 12 12).1.toNat ≤ 5)

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
  probeStretch gpuRenderer swapchainFmt
  probeLayerClip gpuRenderer swapchainFmt
  probeBackdrop gpuRenderer engine font swapchainFmt
  probeRefraction gpuRenderer swapchainFmt
  probeSquircle gpuRenderer swapchainFmt
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
