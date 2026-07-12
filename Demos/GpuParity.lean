import Compose

/-!
# gpu-parity (`Demos/GpuParity.lean`)

The M-d GPU↔SDL parity diff: records one display list per scene, renders it
through `GpuRenderer.renderOffscreen` AND the software-SDL backend at the same
size, and asserts per-scene pixel-difference bounds (mean absolute RGB error
and the fraction of grossly different pixels). The backends anti-alias
differently by design — analytic SDF coverage vs 1-px feathered tessellation —
so edges may disagree; the tolerances bound that disagreement and catch any
real divergence (wrong geometry, color, blending, or clipping).

Text renders the same recorded coordinates through two `Ttf.Text` handles (a
text handle is bound to the engine that created it: GPU-engine vs
renderer-engine), so glyph rasterization itself is compared too.

Real driver only (SDL_GPU has no dummy backend) — run `lake exe gpu-parity`
locally; `scripts/smoke-gpu.sh` runs it after `gpu-probe`.
-/

namespace Demos.GpuParity

open Sdl.Gpu Compose Compose.Draw

/-- Scene extent (all scenes render at this size on both backends). -/
private def W : Nat := 220
private def H : Nat := 120

initialize failures : IO.Ref Nat ← IO.mkRef 0

private def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  ok: {name}"
  else
    failures.modify (· + 1)
    IO.println s!"  FAIL: {name}"

/-- One RGB pixel. -/
private abbrev Px := UInt8 × UInt8 × UInt8

/-- Largest channel distance of two pixels. -/
private def dist (a b : Px) : Nat :=
  let c := fun (x y : UInt8) => (max x y - min x y).toNat
  max (c a.1 b.1) (max (c a.2.1 b.2.1) (c a.2.2 b.2.2))

/-- Shift-tolerant distance at `(x, y)`: pixel `a(x,y)` against its best match
in `b`'s 3×3 neighborhood, symmetrically (the larger of the two directions —
Hausdorff-style, so a feature missing from either image still registers). The
backends place AA edges half a pixel apart by convention (feather ring outside
the silhouette vs centered SDF coverage), which a plain per-pixel diff reports
as a large error on every edge; matching against the neighborhood cancels the
convention shift while wrong geometry, color, blending, or clipping — which
have no nearby match — still show at full magnitude. -/
private def shiftDist (a b : Array Px) (x y : Nat) : Nat := Id.run do
  let side := fun (p : Array Px) (q : Array Px) => Id.run do
    let mut best := 255
    for dy in [0, 1, 2] do
      for dx in [0, 1, 2] do
        let nx := min (W - 1) (max 0 (x + dx) - 1)
        let ny := min (H - 1) (max 0 (y + dy) - 1)
        best := min best (dist p[y * W + x]! q[ny * W + nx]!)
    return best
  return max (side a b) (side b a)

/-- Render `list` through both backends and diff the pixels. Asserts on the
shift-tolerant metric: mean ≤ `meanTol` and the fraction of pixels off by more
than 48 ≤ `grossTol`. The raw per-pixel mean/max print alongside (informational
— they mostly measure the AA edge-convention difference). -/
private def compare (name : String) (r : Compose.Draw.Gpu.GpuRenderer) (bgra : Bool)
    (ren : Sdl.Renderer) (clear : Color) (gpuList sdlList : DisplayList)
    (meanTol grossTol : Float) : IO Unit := do
  let gpuBytes ← r.renderOffscreen clear gpuList W H
  let (cr, cg, cb, ca) := clear.toBytes
  ren.setDrawColor cr cg cb ca
  ren.clear
  SdlBackend.execute ren sdlList
  let shot ← ren.readPixels
  let mut gpu : Array Px := Array.emptyWithCapacity (W * H)
  let mut sdl : Array Px := Array.emptyWithCapacity (W * H)
  for y in [0:H] do
    for x in [0:W] do
      let o := (y * W + x) * 4
      gpu := gpu.push (if bgra
        then (gpuBytes.get! (o + 2), gpuBytes.get! (o + 1), gpuBytes.get! o)
        else (gpuBytes.get! o, gpuBytes.get! (o + 1), gpuBytes.get! (o + 2)))
      let s ← shot.readPixel (Int32.ofNat x) (Int32.ofNat y)
      sdl := sdl.push (s.r, s.g, s.b)
  let mut rawSum := 0
  let mut rawMax := 0
  let mut shiftSum := 0
  let mut shiftMax := 0
  let mut gross := 0
  for y in [0:H] do
    for x in [0:W] do
      let dRaw := dist gpu[y * W + x]! sdl[y * W + x]!
      rawSum := rawSum + dRaw
      rawMax := max rawMax dRaw
      let d := if dRaw == 0 then 0 else shiftDist gpu sdl x y
      shiftSum := shiftSum + d
      shiftMax := max shiftMax d
      if d > 48 then
        gross := gross + 1
        if (← IO.getEnv "COMPOSE_PARITY_DUMP").isSome && gross ≤ 12 then
          IO.println s!"    gross @({x},{y}): gpu={gpu[y * W + x]!} sdl={sdl[y * W + x]!} d={d}"
  let total := W * H
  let mean := shiftSum.toFloat / total.toFloat
  let grossFrac := gross.toFloat / total.toFloat
  IO.println s!"  {name}: shifted mean={mean} max={shiftMax} gross={gross}/{total} \
(raw mean={rawSum.toFloat / total.toFloat} max={rawMax})"
  check s!"{name}: shifted mean ≤ {meanTol}" (mean ≤ meanTol)
  check s!"{name}: shifted gross ≤ {grossTol * 100}%" (grossFrac ≤ grossTol)

/-- `compare` with one shared list (every scene but text). -/
private def compareScene (name : String) (r : Compose.Draw.Gpu.GpuRenderer) (bgra : Bool)
    (ren : Sdl.Renderer) (clear : Color) (body : DrawM Unit)
    (meanTol grossTol : Float) : IO Unit := do
  let (list, _) ← DrawScope.record {} body
  compare name r bgra ren clear list list meanTol grossTol

def run : IO UInt32 := do
  IO.println "== gpu-parity: GPU vs SDL pixel diff =="
  Sdl.init .video
  let dev ← createDevice .msl (debugMode := true)
  dev.setAllowedFramesInFlight 2
  let window ← Sdl.createWindow "gpu-parity" 256 160
  dev.claimWindow window
  let swapchainFmt ← dev.getSwapchainTextureFormat window
  let bgra := swapchainFmt == .b8g8r8a8Unorm
  let gpuR ← Compose.Draw.Gpu.GpuRenderer.create dev window
  let sdlWin ← Sdl.createWindow "gpu-parity-sdl" (Int32.ofNat W) (Int32.ofNat H)
  let ren ← Sdl.createRenderer sdlWin (some Sdl.softwareRenderer)
  let scene := compareScene (r := gpuR) (bgra := bgra) (ren := ren)

  -- Crisp solid rects: the exact fast path on both sides (fillRect vs an
  -- integer-aligned SDF quad) — near-zero tolerance.
  scene "crisp rects + clip" ⟨0, 0, 0, 1⟩
    (do
      DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨60, 40⟩
      DrawScope.drawRect (.solid (Color.green.withAlpha 0.5)) ⟨40, 30⟩ ⟨60, 40⟩
      DrawScope.clipRect ⟨120, 20, 170, 70⟩ do
        DrawScope.drawRect (.solid .white) ⟨100, 10⟩ ⟨100, 100⟩)
    (meanTol := 0.1) (grossTol := 0.001)

  -- Anti-aliased shapes: fills, strokes, arc, lines. Edges differ by design
  -- (SDF coverage vs feather ring) — bounded, not eliminated.
  scene "aa shapes" ⟨0.1, 0.1, 0.1, 1⟩
    (do
      DrawScope.drawRoundRect (.solid .blue) (RoundRect.circular ⟨10, 10, 60, 60⟩ 12)
      DrawScope.drawRoundRect (.solid .white) (RoundRect.circular ⟨70, 10, 120, 60⟩ 12)
        (.stroke 3)
      DrawScope.drawCircle (.solid .yellow) ⟨150, 35⟩ 22
      DrawScope.drawCircle (.solid .red) ⟨195, 35⟩ 18 (.stroke 4)
      DrawScope.drawArc (.solid .green) ⟨40, 90⟩ 18 0.5 4.5 5
      DrawScope.drawLine (.solid .white) ⟨80, 80⟩ ⟨140, 80⟩ 3
      DrawScope.drawLine (.solid .white) ⟨90, 110⟩ ⟨150, 85⟩ 3)
    (meanTol := 2.0) (grossTol := 0.02)

  -- Gradients: a 2-stop (GPU quad path) and a 3-stop (identical tessellated
  -- mesh on both backends).
  scene "gradients" ⟨0, 0, 0, 1⟩
    (do
      DrawScope.drawRect (.gradient .red .blue ⟨10, 0⟩ ⟨100, 0⟩) ⟨10, 10⟩ ⟨90, 40⟩
      DrawScope.drawRoundRect
        (.linearGradient #[(0, Color.red), (0.5, .green), (1, .blue)] ⟨110, 0⟩ ⟨210, 0⟩)
        (RoundRect.circular ⟨110, 10, 210, 50⟩ 8))
    (meanTol := 1.6) (grossTol := 0.013)

  -- Shadows: analytic Gaussian vs sampled feathered rings under a filled
  -- surface (the Material lowering shape: offset e/2, blur e).
  scene "shadows" ⟨1, 1, 1, 1⟩
    (do
      let rr := RoundRect.circular ⟨40, 30, 120, 80⟩ 10
      DrawScope.drawShape (.rrShadow rr ⟨0, 3⟩ 6 (Color.black.withAlpha 0.25))
      DrawScope.drawRoundRect (.solid .red) rr
      DrawScope.drawShape
        (.rrShadow (RoundRect.ofRect ⟨150, 30, 200, 80⟩) ⟨0, 0⟩ 8 .black))
    (meanTol := 1.8) (grossTol := 0.008)

  -- Layers + the bounded ripple: disjoint layer content (SDL's flatten equals
  -- the GPU composite when nothing self-overlaps) and a rounded-clipped
  -- oversized circle (geometric clip on SDL, masked quad on the GPU).
  -- Rounded-clipping of *arbitrary* content is deliberately absent: SDL
  -- rect-approximates it while the GPU masks exactly (a documented
  -- divergence, pinned GPU-side by gpu-probe step ⑧).
  scene "layer + ripple clip" ⟨0, 0, 0, 1⟩
    (do
      DrawScope.withLayer ⟨10, 10, 100, 60⟩ 0.5 do
        DrawScope.drawRect (.solid .red) ⟨10, 10⟩ ⟨40, 20⟩
        DrawScope.drawRect (.solid .blue) ⟨60, 35⟩ ⟨40, 20⟩
      DrawScope.clipRoundRect (RoundRect.circular ⟨10, 70, 60, 115⟩ 10) do
        DrawScope.drawCircle (.solid .yellow) ⟨35, 92⟩ 40)
    (meanTol := 0.5) (grossTol := 0.005)

  -- Vector paths (M-e1/M-e2): fills and strokes lower to the SAME band-sweep
  -- mesh on both backends, so geometry, winding, and color bugs show at full
  -- magnitude. What remains is the two triangle rasterizers' sub-pixel phase
  -- on thin AA geometry (feather ramps, bands at curve extrema — observed
  -- shifted mean ≈ 1.1), the same family as the mesh-drawn "gradients" (1.6)
  -- and "aa shapes" (2.0) scenes.
  scene "paths" ⟨0, 0, 0, 1⟩
    (do
      DrawScope.drawPath (.solid .yellow) (Path.build (fillRule := .evenOdd) do
        PathM.addOval ⟨10, 10, 70, 70⟩
        PathM.addOval ⟨25, 25, 55, 55⟩)
      DrawScope.drawPath (.solid .red) (Path.build (body := do
        let pt (k : Nat) : Offset :=
          let pi : Float := 3.14159265358979323846
          let a := -pi / 2 + k.toFloat * 4 * pi / 5
          ⟨110 + 28 * (Float.cos a).toFloat32, 50 + 28 * (Float.sin a).toFloat32⟩
        PathM.moveTo (pt 0)
        for k in [1:5] do
          PathM.lineTo (pt k)
        PathM.close))
      DrawScope.drawPath (.gradient .red .blue ⟨150, 0⟩ ⟨215, 0⟩) (Path.build do
        PathM.moveTo ⟨155, 60⟩
        PathM.cubicTo ⟨150, 15⟩ ⟨215, 15⟩ ⟨205, 60⟩
        PathM.cubicTo ⟨215, 105⟩ ⟨150, 105⟩ ⟨155, 60⟩
        PathM.close)
      DrawScope.drawPath (.solid .white) (Path.build do
        PathM.moveTo ⟨10, 90⟩; PathM.lineTo ⟨40, 112⟩; PathM.lineTo ⟨70, 90⟩)
        (.stroke { width := 3 }))
    (meanTol := 1.5) (grossTol := 0.01)

  -- Path strokes + clipPath (M-e2): dashed round caps, miter joins, and the
  -- dual-winding clipped fill — again identical meshes on both backends, so
  -- only rasterizer sub-pixel phase remains (same tolerance family as the
  -- "paths" scene above; strokes are almost all thin AA geometry).
  scene "path strokes" ⟨0, 0, 0, 1⟩
    (do
      DrawScope.drawPath (.solid .white) (Path.build do
        PathM.moveTo ⟨10, 20⟩; PathM.lineTo ⟨50, 55⟩; PathM.lineTo ⟨90, 20⟩)
        (.stroke { width := 7, cap := .round, join := .round, dash := some (#[16, 9], 4) })
      DrawScope.drawPath (.solid .yellow) (Path.build do
        PathM.addRect ⟨15, 75, 60, 105⟩)
        (.stroke { width := 6, join := .miter })
      DrawScope.drawPath (.gradient .red .blue ⟨105, 0⟩ ⟨160, 0⟩) (Path.build do
        PathM.moveTo ⟨105, 95⟩; PathM.quadTo ⟨132, 55⟩ ⟨160, 95⟩)
        (.stroke { width := 5, cap := .square, join := .bevel })
      DrawScope.clipPath (Path.build do PathM.addOval ⟨140, 10, 210, 70⟩) do
        DrawScope.drawPath (.solid .green) (Path.build do
          PathM.addRect ⟨120, 5, 215, 45⟩))
    (meanTol := 1.5) (grossTol := 0.01)

  -- Text: same coordinates, two engine-bound handles. The GPU snaps the run
  -- origin to whole pixels (integers here, so no offset) and both rasterize
  -- through SDL_ttf — differences are glyph-blending only.
  Sdl.Ttf.init
  let font ← Sdl.Ttf.openFont "assets/fonts/Roboto-Regular.ttf" 16
  let gpuEngine ← Sdl.Ttf.createGpuTextEngine dev
  let sdlEngine ← Sdl.Ttf.createRendererTextEngine ren
  let gpuText ← gpuEngine.createText font "The quick brown fox 0123"
  let sdlText ← sdlEngine.createText font "The quick brown fox 0123"
  let textBody (t : Sdl.Ttf.Text) : DrawM Unit :=
    DrawScope.drawText { text := t, string := "The quick brown fox 0123", color := .white }
      ⟨15, 40⟩
  let (gpuList, _) ← DrawScope.record {} (textBody gpuText)
  let (sdlList, _) ← DrawScope.record {} (textBody sdlText)
  compare "text" gpuR bgra ren ⟨0, 0, 0, 1⟩ gpuList sdlList
    (meanTol := 0.5) (grossTol := 0.005)

  let stats ← Compose.Draw.Gpu.frameStats.get
  IO.println s!"  last frame stats: {stats.brief}"
  check "frame stats populated" (stats.drawCalls > 0)

  dev.releaseWindow window
  let n ← failures.get
  IO.println (if n == 0 then "== gpu-parity: all scenes within tolerance =="
              else s!"== gpu-parity: {n} FAILED ==")
  return UInt32.ofNat n

end Demos.GpuParity

def main : IO UInt32 := Demos.GpuParity.run
