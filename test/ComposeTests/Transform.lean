import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Transform group (`test/ComposeTests/Transform.lean`)

Headless coverage for M-g graphics-layer transforms. The first scenario
probes the SDL semantics the backend's real offscreen layers rest on
(`.target` textures + transparent clear + `.blendPremultiplied` composite
under the dummy driver); the rest exercise `withGraphicsLayer` pixels through
the SDL backend (rotation quadrants, scale, snapped translation, group
opacity without double-blend, nesting, clip semantics inside vs outside the
layer, rotated images), the recorded IR (brief golden, mapped damage bounds),
and `Modifier.graphicsLayer` through the layout walk (pixels follow the
angle; meshes don't re-tessellate as it animates). `Affine`, `toAffine`, and
`snapComposite` are `#guard`-pinned in src.
-/

namespace Tests.Transform
open Compose Compose.Test Compose.Draw Compose.Draw.DrawScope Tests.Harness

private def mkRen (w h : Int32) : IO Sdl.Renderer := do
  let win ← Sdl.createWindow "compose-transform" w h
  Sdl.createRenderer win (some Sdl.softwareRenderer)

private def clear (ren : Sdl.Renderer) (r g b : UInt8) : IO Unit := do
  ren.setDrawColor r g b 255
  ren.clear

/-- The SDL assumptions behind real offscreen layers, step by step: render
translucent content onto a transparent `.target` texture (`.blend` yields
premultiplied texels), then composite with `.blendPremultiplied`. -/
private def probePremultipliedComposite : IO Unit := do
  let ren ← mkRen 32 32
  clear ren 0 255 0                       -- green background
  let tex ← ren.createTexture .rgba32 .target 64 64
  ren.setTarget (some tex)
  ren.setClipRect none
  ren.setDrawColor 0 0 0 0
  ren.clear                               -- transparent (clear ignores blending)
  ren.setDrawBlendMode .blend
  ren.setDrawColor 255 0 0 128            -- half-alpha red content
  ren.fillRect (some ⟨0, 0, 16, 16⟩)
  ren.setTarget none
  tex.setBlendMode .blendPremultiplied
  ren.texture tex (some ⟨0, 0, 16, 16⟩) (some ⟨0, 0, 16, 16⟩)
  let shot ← ren.readPixels
  -- premul texel (128, 0, 0, 128) over green: (128, 255·(1−α)=127, 0)
  check "probe: premultiplied composite over green"
    (colorNear (← shot.readPixel 8 8) 128 127 0 (tol := 3))
  check "probe: outside the composite untouched"
    (colorNear (← shot.readPixel 24 24) 0 255 0)

/-- 90° rotation about the layer center: exact quadrant swap (left-half red /
right-half blue content becomes top red / bottom blue). -/
private def rotation90 : IO Unit := do
  let ren ← mkRen 64 64
  clear ren 0 0 0
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 40, 40⟩ { rotationZ := 90 } do
      drawRect (.solid .red) ⟨0, 0⟩ ⟨20, 40⟩
      drawRect (.solid .blue) ⟨20, 0⟩ ⟨20, 40⟩
  let shot ← ren.readPixels
  check "rot90: top half red" (colorNear (← shot.readPixel 20 10) 255 0 0)
  check "rot90: bottom half blue" (colorNear (← shot.readPixel 20 30) 0 0 255)
  check "rot90: corner quadrant red" (colorNear (← shot.readPixel 5 5) 255 0 0)
  check "rot90: outside the layer untouched" (colorNear (← shot.readPixel 55 55) 0 0 0)

/-- 2× scale about the layer center: the content quarter grows to cover the
whole (shifted) bounds. -/
private def scale2x : IO Unit := do
  let ren ← mkRen 64 64
  clear ren 0 0 0
  DrawScope.run ren {} do
    translate ⟨20, 20⟩ do
      withGraphicsLayer ⟨0, 0, 20, 20⟩ { scaleX := 2, scaleY := 2 } do
        drawRect (.solid .red) ⟨0, 0⟩ ⟨10, 10⟩
  let shot ← ren.readPixels
  -- pivot (30,30); the red (20,20)-(30,30) target rect maps to (10,10)-(30,30)
  check "scale: near the mapped min corner red" (colorNear (← shot.readPixel 13 13) 255 0 0)
  check "scale: near the pivot red" (colorNear (← shot.readPixel 27 27) 255 0 0)
  check "scale: beyond the pivot untouched" (colorNear (← shot.readPixel 35 35) 0 0 0)

/-- A whole-pixel translation snaps (`Affine.snapComposite`): the composite is
a crisp 1:1 copy at the translated origin. -/
private def snappedTranslation : IO Unit := do
  let ren ← mkRen 32 32
  clear ren 0 0 0
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 10, 10⟩ { translationX := 5, translationY := 3 } do
      drawRect (.solid .white) ⟨0, 0⟩ ⟨10, 10⟩
  let shot ← ren.readPixels
  check "snap: interior white" (colorNear (← shot.readPixel 10 8) 255 255 255)
  check "snap: first covered column crisp" (colorNear (← shot.readPixel 5 8) 255 255 255)
  check "snap: column left of it untouched" (colorNear (← shot.readPixel 3 8) 0 0 0)
  check "snap: last covered row crisp" (colorNear (← shot.readPixel 10 12) 255 255 255)
  check "snap: row below untouched" (colorNear (← shot.readPixel 10 14) 0 0 0)

/-- Group opacity inside a *transformed* layer composites once on SDL too:
self-overlapping opaque content at layer alpha 0.5 reads uniformly ≈128 —
the double-blend the flattening approximation would show is gone. -/
private def groupOpacityNoDoubleBlend : IO Unit := do
  let ren ← mkRen 64 32
  clear ren 0 0 0
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 30, 20⟩ { alpha := 0.5, translationX := 2 } do
      drawRect (.solid .white) ⟨0, 0⟩ ⟨20, 20⟩
      drawRect (.solid .white) ⟨10, 0⟩ ⟨20, 20⟩
  let shot ← ren.readPixels
  check "group alpha: non-overlap ≈ 50%" (colorNear (← shot.readPixel 7 10) 128 128 128)
  check "group alpha: overlap also ≈ 50% (no double blend)"
    (colorNear (← shot.readPixel 17 10) 128 128 128)

/-- Nesting: an untransformed alpha layer inside a rotated layer folds its
alpha into the rotated content exactly once. -/
private def nestedLayers : IO Unit := do
  let ren ← mkRen 64 64
  clear ren 0 0 0
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 40, 40⟩ { rotationZ := 90 } do
      withLayer ⟨0, 0, 40, 40⟩ 0.5 do
        drawRect (.solid .red) ⟨0, 0⟩ ⟨40, 40⟩
  let shot ← ren.readPixels
  check "nested: rotated content at combined alpha"
    (colorNear (← shot.readPixel 20 20) 128 0 0 (tol := 3))

/-- Clip semantics: an *enclosing* clip scissors the composite (target
coordinates); a clip *inside* the layer bakes into the texture and rotates
with the content. -/
private def clipSemantics : IO Unit := do
  let ren ← mkRen 64 64
  clear ren 0 0 0
  DrawScope.run ren {} do
    clipRect ⟨0, 0, 20, 40⟩ do
      withGraphicsLayer ⟨0, 0, 40, 40⟩ { rotationZ := 90 } do
        drawRect (.solid .red) ⟨0, 0⟩ ⟨40, 40⟩
  let shot ← ren.readPixels
  check "enclosing clip: inside kept" (colorNear (← shot.readPixel 10 20) 255 0 0)
  check "enclosing clip: composite scissored" (colorNear (← shot.readPixel 30 20) 0 0 0)
  clear ren 0 0 0
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 40, 40⟩ { rotationZ := 90 } do
      clipRect ⟨0, 0, 20, 40⟩ do
        drawRect (.solid .red) ⟨0, 0⟩ ⟨40, 40⟩
  let shot ← ren.readPixels
  check "inner clip: rotates with the content (top half red)"
    (colorNear (← shot.readPixel 20 10) 255 0 0)
  check "inner clip: bottom half empty" (colorNear (← shot.readPixel 20 30) 0 0 0)

/-- An image drawn inside a rotated layer: the four 20×-scaled quadrants land
rotated (texture-in-texture through the composite). -/
private def rotatedImage : IO Unit := do
  let ren ← mkRen 64 64
  clear ren 0 0 0
  let img ← ImageBitmap.ofPixels 2 2 fun x y =>
    match x, y with
    | 0, 0 => .red | 1, 0 => .green
    | 0, 1 => .blue | _, _ => .white
  DrawScope.run ren {} do
    withGraphicsLayer ⟨0, 0, 40, 40⟩ { rotationZ := 90 } do
      drawImage img ⟨0, 0, 40, 40⟩ (sampling := .nearest)
  let shot ← ren.readPixels
  -- screen (sx,sy) samples content (sy, 40−sx)
  check "image rot90: (30,10) was top-left red" (colorNear (← shot.readPixel 30 10) 255 0 0)
  check "image rot90: (30,30) was top-right green" (colorNear (← shot.readPixel 30 30) 0 255 0)
  check "image rot90: (10,10) was bottom-left blue" (colorNear (← shot.readPixel 10 10) 0 0 255)
  check "image rot90: (10,30) was bottom-right white"
    (colorNear (← shot.readPixel 10 30) 255 255 255)

/-- Recorded IR: the transform rides the layer prim (brief golden) and damage
bounds map through it. -/
private def irGoldens : IO Unit := do
  let (list, _) ← DrawScope.record {} do
    withGraphicsLayer ⟨0, 0, 20, 20⟩ { translationX := 5, translationY := 3 } do
      drawRect (.solid .red) ⟨0, 0⟩ ⟨20, 20⟩
  checkEq "transformed layer brief" (list.map (·.brief)).toList
    ["layer @(0,0) bounds=(0,0,20,20) a=1 t=[1,0,0,1,5,3]\n\
      \x20 rect @(0,0) #ff0000ff tl=(0,0) sz=20x20"]
  check "damage bounds map through the transform"
    (list[0]!.bounds == some ⟨5, 3, 25, 23⟩)
  -- identity settings record nothing
  let (flat, _) ← DrawScope.record {} do
    withGraphicsLayer ⟨0, 0, 20, 20⟩ {} do
      drawRect (.solid .red) ⟨0, 0⟩ ⟨20, 20⟩
  check "identity graphics layer records no layer prim"
    (flat.size == 1 && (match flat[0]! with | .rect .. => true | _ => false))

/-- `Modifier.graphicsLayer` through the layout walk: pixels follow the angle
across recompositions, and animating the angle re-tessellates nothing (the
mesh cache keys on the untransformed shape). -/
private def modifierRotation : IO Unit := do
  let angle ← MutableState.create (0 : Float32)
  runComposeTest
    (Tests.restartable 1 do
      let a ← angle.get
      Box (modifier := Modifier.graphicsLayer (rotationZ := a) |>.size 40 40) do
        Row do
          Box (modifier := Modifier.size 20 40 |>.background Color.red (.rounded 6))
          Box (modifier := Modifier.size 20 40 |>.background Color.blue))
    do
      awaitIdle
      let c0 ← Draw.tessellationCount.get
      check "modifier: untransformed left red" (colorNear (← pixel 10 20) 255 0 0)
      check "modifier: untransformed right blue" (colorNear (← pixel 30 20) 0 0 255)
      angle.set 90
      awaitIdle
      check "modifier: rotated top red" (colorNear (← pixel 20 10) 255 0 0)
      check "modifier: rotated bottom blue" (colorNear (← pixel 20 30) 0 0 255)
      angle.set 45
      awaitIdle
      angle.set 60
      awaitIdle
      checkEq "animating the angle re-tessellates nothing"
        (← Draw.tessellationCount.get) c0

/-- The Transform group. -/
def run : IO Unit := do
  Sdl.init .video
  scenario "probe: premultiplied offscreen composite" probePremultipliedComposite
  scenario "rotation 90° quadrants" rotation90
  scenario "scale 2× about the center" scale2x
  scenario "whole-pixel translation snaps" snappedTranslation
  scenario "group opacity without double blend" groupOpacityNoDoubleBlend
  scenario "nested layers" nestedLayers
  scenario "clip inside vs outside the layer" clipSemantics
  scenario "rotated image" rotatedImage
  scenario "IR goldens and mapped bounds" irGoldens
  scenario "Modifier.graphicsLayer through the layout walk" modifierRotation

end Tests.Transform
