import Compose
import ComposeTests.Harness

/-!
# PathDraw group (`test/ComposeTests/PathDraw.lean`)

Headless pixel + IR coverage for vector paths (M-e1 fills, M-e2 strokes +
`clipPath`): `drawPath` fills and strokes through the band-sweep tessellator
on the software renderer (donut hole, fill-rule discrimination, gradients,
ambient translate/clip/alpha, stroked outlines, dashed round caps, exact
path-clipped fills), the recorded brief goldens, and seeded random-polygon
fuzz of the plain and clipped tessellators against the geometric oracle
(`pathFillAgreesWithOracle` / `pathFillClippedAgreesWithOracle` — the same
agreement the compile-time corpus in `PathFill.lean` pins for hand-picked
shapes).
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

  -- 5. stroke: a closed outline covers the boundary (miter corners included)
  -- and leaves the interior open
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.white) (Path.build do addRect ⟨20, 20, 80, 80⟩)
        (.stroke { width := 4 })
    let shot ← ren.readPixels
    check "path stroke: edge covered" (colorNear (← shot.readPixel 50 20) 255 255 255)
    check "path stroke: miter corner covered" (colorNear (← shot.readPixel 19 19) 255 255 255)
    check "path stroke: interior open" (colorNear (← shot.readPixel 50 50) 0 0 0)

  -- 6. dashed round-cap stroke: on-runs paint, gaps stay clear
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawPath (.solid Color.white) (Path.build do moveTo ⟨20, 60⟩; lineTo ⟨100, 60⟩)
        (.stroke { width := 6, cap := .round, dash := some (#[20, 20], 0) })
    let shot ← ren.readPixels
    check "dash: first on-run painted" (colorNear (← shot.readPixel 30 60) 255 255 255)
    check "dash: gap clear" (colorNear (← shot.readPixel 50 60) 0 0 0)
    check "dash: second on-run painted" (colorNear (← shot.readPixel 70 60) 255 255 255)
    check "dash: stroke thickness reaches off-axis" (colorNear (← shot.readPixel 30 58) 255 255 255)

  -- 7. clipPath: a path fill clips exactly to a circular path (not just its
  -- bounds rectangle)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      clipPath (Path.build do addOval ⟨30, 30, 90, 90⟩) do
        drawPath (.solid Color.red) (Path.build do addRect ⟨0, 0, 128, 128⟩)
    let shot ← ren.readPixels
    check "clipPath: circle interior filled" (colorNear (← shot.readPixel 60 60) 255 0 0)
    check "clipPath: inside bounds, outside circle clear"
      (colorNear (← shot.readPixel 35 35) 0 0 0)
    check "clipPath: outside bounds clear" (colorNear (← shot.readPixel 20 60) 0 0 0)

  -- 8. clipPath across translate: the clip is captured in render-target
  -- coordinates and re-anchored into the draw's local frame
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      clipPath (Path.build do addRect ⟨40, 40, 80, 80⟩) do
        translate ⟨40, 40⟩ do
          drawPath (.solid Color.red) (Path.build do addRect ⟨0, 0, 60, 60⟩)
    let shot ← ren.readPixels
    check "clipPath+translate: intersection filled" (colorNear (← shot.readPixel 60 60) 255 0 0)
    check "clipPath+translate: drawn but clipped region clear"
      (colorNear (← shot.readPixel 90 60) 0 0 0)

  -- 9. IR: the recorded shape specs (brief goldens) for a clipped fill and a
  -- fully-dressed stroke
  do
    let (list, _) ← DrawScope.record {} do
      drawPath (.solid .red) (Path.build (fillRule := .evenOdd) do addRect ⟨2, 2, 22, 14⟩)
      clipPath (Path.build do addRect ⟨4, 4, 20, 20⟩) do
        drawPath (.solid .red) (Path.build (fillRule := .evenOdd) do addRect ⟨2, 2, 22, 14⟩)
      drawPath (.solid .white) (Path.build do addRect ⟨0, 0, 10, 10⟩)
        (.stroke { width := 2, cap := .round, join := .bevel, dash := some (#[4, 2], 1) })
    checkEq "path brief goldens" (list.map (·.brief)).toList
      [ "shape @(0,0) pathFill v=5 (2,2,22,14) evenOdd #ff0000ff"
      , "shape @(0,0) clip=(4,4,20,20) pathFillClipped v=5 (2,2,22,14) evenOdd"
          ++ " clip=v5(4,4,20,20) #ff0000ff"
      , "shape @(0,0) pathStroke v=5 (0,0,10,10) w=2 cap=round join=bevel dash=[2]+1 #ffffffff" ]

  -- 10. fuzz: random 8-gons (both rules) agree with the winding oracle,
  -- plain and clipped by a fixed square
  do
    let mut seed : UInt32 := 0xC0FFEE
    let next : UInt32 → UInt32 := fun s => s * 1664525 + 1013904223
    let clip := Path.build do addRect ⟨10, 10, 54, 54⟩
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
      check s!"fuzz round {round} ({repr rule}): clipped tessellation agrees with oracle"
        (pathFillClippedAgreesWithOracle path clip)

end Tests.PathDraw
