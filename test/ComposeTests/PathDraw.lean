import Compose
import ComposeTests.Harness

/-!
# PathDraw group (`test/ComposeTests/PathDraw.lean`)

Headless pixel + IR coverage for vector paths (M-e1): `drawPath` fills through
the band-sweep tessellator on the software renderer (donut hole, fill-rule
discrimination, gradients, ambient translate/clip/alpha), the recorded
`pathFill` brief golden, the provisional polyline stroke, and a seeded
random-polygon fuzz of the tessellator against the geometric oracle
(`pathFillAgreesWithOracle` — the same agreement the compile-time corpus in
`PathFill.lean` pins for hand-picked shapes).
-/

namespace Tests.PathDraw
open Compose Compose.Draw Compose.Draw.DrawScope Compose.Draw.PathM Tests.Harness

private def mkRen (w h : Int32) : IO Sdl.Renderer := do
  let win ← Sdl.createWindow "compose-path" w h
  Sdl.createRenderer win (some Sdl.softwareRenderer)

private def clearBlack (ren : Sdl.Renderer) : IO Unit := do
  ren.setDrawColor 0 0 0 255
  ren.clear

/-- Two concentric ovals under even-odd: a ring with a real hole. -/
private def donut : Path :=
  Path.build (fillRule := .evenOdd) do
    addOval ⟨20, 20, 80, 80⟩
    addOval ⟨35, 35, 65, 65⟩

/-- Self-intersecting five-point star around `(40, 40)`. -/
private def star (rule : FillRule) : Path :=
  Path.build (fillRule := rule) (body := do
    let pt (k : Nat) : Offset :=
      let pi : Float := 3.14159265358979323846
      let a := -pi / 2 + k.toFloat * 4 * pi / 5
      ⟨40 + 30 * (Float.cos a).toFloat32, 40 + 30 * (Float.sin a).toFloat32⟩
    moveTo (pt 0)
    for k in [1:5] do
      lineTo (pt k)
    close)

/-- The PathDraw group. -/
def run : IO Unit := do
  Sdl.init .video

  -- 1. donut: ring filled, hole and outside untouched
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.red) donut
    let shot ← ren.readPixels
    check "donut: ring filled" (colorNear (← shot.readPixel 50 26) 255 0 0)
    check "donut: hole untouched" (colorNear (← shot.readPixel 50 50) 0 0 0)
    check "donut: outside untouched" (colorNear (← shot.readPixel 8 8) 0 0 0)

  -- 2. fill rules: the star center fills under nonZero, not under evenOdd
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.green) (star .nonZero)
    let shot ← ren.readPixels
    check "star nonZero: center filled" (colorNear (← shot.readPixel 40 40) 0 255 0)
    check "star nonZero: top tip filled" (colorNear (← shot.readPixel 40 14) 0 255 0)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.green) (star .evenOdd)
    let shot ← ren.readPixels
    check "star evenOdd: center is the pentagon hole" (colorNear (← shot.readPixel 40 40) 0 0 0)
    check "star evenOdd: point arms still fill" (colorNear (← shot.readPixel 40 14) 0 255 0)

  -- 3. gradient fill across a path (endpoint colors at the extremes)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.gradient .red .blue ⟨10, 0⟩ ⟨90, 0⟩) (Path.build do
        addRect ⟨10, 10, 90, 50⟩)
    let shot ← ren.readPixels
    check "path gradient: left ≈ red" (colorNear (← shot.readPixel 12 30) 255 0 0 24)
    check "path gradient: right ≈ blue" (colorNear (← shot.readPixel 88 30) 0 0 255 24)

  -- 4. ambient state: translate + clip + alpha resolve like any other shape
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      translate ⟨40, 40⟩ do
        clipRect ⟨0, 0, 30, 60⟩ do
          withAlpha 0.5 do
            drawPath (.solid Color.red) (Path.build do addRect ⟨0, 0, 60, 20⟩)
    let shot ← ren.readPixels
    check "path translate+alpha: inside clip ≈ 50% red"
      (colorNear (← shot.readPixel 50 50) 128 0 0)
    check "path clip: right of clip untouched" (colorNear (← shot.readPixel 75 50) 0 0 0)
    check "path translate: untranslated origin untouched"
      (colorNear (← shot.readPixel 10 10) 0 0 0)

  -- 5. provisional stroke: a polyline stroke marks the boundary, not the interior
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.white) (Path.build do addRect ⟨20, 20, 80, 80⟩) (.stroke 4)
    let shot ← ren.readPixels
    check "path stroke: edge covered" (colorNear (← shot.readPixel 50 20) 255 255 255)
    check "path stroke: interior open" (colorNear (← shot.readPixel 50 50) 0 0 0)

  -- 6. IR: fill records a pathFill shape spec (brief golden); stroke records
  -- a mesh prim (no spec until the real stroker)
  do
    let (list, _) ← DrawScope.record {} do
      drawPath (.solid .red) (Path.build (fillRule := .evenOdd) do addRect ⟨2, 2, 22, 14⟩)
      drawPath (.solid .white) (Path.build do addRect ⟨0, 0, 10, 10⟩) (.stroke 2)
    checkEq "pathFill brief" (list.map (·.brief)).toList
      [ "shape @(0,0) pathFill v=5 (2,2,22,14) evenOdd #ff0000ff"
      , "mesh @(0,0) v=16 t=24" ]

  -- 7. fuzz: random 8-gons (both rules) agree with the winding oracle
  do
    let mut seed : UInt32 := 0xC0FFEE
    let next : UInt32 → UInt32 := fun s => s * 1664525 + 1013904223
    for round in [0:10] do
      let mut pts : Array Offset := #[]
      for _ in [0:8] do
        seed := next seed
        let x := 4 + (seed >>> 8).toNat % 60
        seed := next seed
        let y := 4 + (seed >>> 8).toNat % 60
        pts := pts.push ⟨x.toFloat32, y.toFloat32⟩
      let rule := if round % 2 == 0 then FillRule.nonZero else .evenOdd
      let path := Path.build (fillRule := rule) (body := do
        moveTo pts[0]!
        for i in [1:pts.size] do
          lineTo pts[i]!
        close)
      check s!"fuzz round {round} ({repr rule}): tessellation agrees with oracle"
        (pathFillAgreesWithOracle path)

end Tests.PathDraw
