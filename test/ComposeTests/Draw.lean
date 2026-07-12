import Compose
import ComposeTests.Harness

/-!
# Draw-stack pixel tests (`test/ComposeTests/Draw.lean`)

Headless pixel assertions for `Compose/Ui/Draw/*`. Renders known scenes with the
software renderer under the dummy video driver, reads them back with
`Renderer.readPixels`, and probes individual pixels — the approach lean-sdl3's
own suite proves works headless. Covers: solid/overlapping fills, rounded-rect
corners, circle fill + alpha blend, clip nesting + restore, translate, alpha
scaling, and linear-gradient endpoints.

Run: `SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test`.
-/

namespace Tests.Draw
open Compose Compose.Draw Compose.Draw.DrawScope Tests.Harness

/-- A fresh software renderer of the given size (the window is kept alive by the
renderer's owner chain). -/
private def mkRen (w h : Int32) : IO Sdl.Renderer := do
  let win ← Sdl.createWindow "compose-draw" w h
  Sdl.createRenderer win (some Sdl.softwareRenderer)

/-- Clear the renderer to opaque black. -/
private def clearBlack (ren : Sdl.Renderer) : IO Unit := do
  ren.setDrawColor 0 0 0 255
  ren.clear

/-- The Draw group. -/
def run : IO Unit := do
  Sdl.init .video

  -- 1. solid rect fill (exact color) + overlap (top wins)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawRect (.solid Color.red) ⟨10, 10⟩ ⟨40, 40⟩
      drawRect (.solid Color.green) ⟨20, 20⟩ ⟨40, 40⟩
    let shot ← ren.readPixels
    check "solid fill: background stays black" (colorNear (← shot.readPixel 2 2) 0 0 0)
    check "solid fill: red region exact" (colorNear (← shot.readPixel 12 12) 255 0 0)
    check "overlap: top (green) wins" (colorNear (← shot.readPixel 30 30) 0 255 0)

  -- 2. rounded rect: corner outside radius is background; center/edges filled
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawRoundRect (.solid Color.red) (RoundRect.circular ⟨10, 10, 60, 60⟩ 14)
    let shot ← ren.readPixels
    check "roundRect: center filled" (colorNear (← shot.readPixel 40 40) 255 0 0)
    check "roundRect: top-edge midpoint filled" (colorNear (← shot.readPixel 40 11 ) 255 0 0)
    check "roundRect: left-edge midpoint filled" (colorNear (← shot.readPixel 11 40) 255 0 0)
    check "roundRect: outside corner is background" (colorNear (← shot.readPixel 11 11) 0 0 0)

  -- 3. circle fill: center filled, outside background; and half-alpha blend
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawCircle (.solid Color.red) ⟨40, 40⟩ 20
    let shot ← ren.readPixels
    check "circle: center filled" (colorNear (← shot.readPixel 40 40) 255 0 0)
    check "circle: outside corner background" (colorNear (← shot.readPixel 5 5) 0 0 0)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawCircle (.solid (Color.red.withAlpha 0.5)) ⟨40, 40⟩ 20
    let shot ← ren.readPixels
    -- red at 50% over black ≈ (128, 0, 0), tolerance ±2
    check "circle: half-alpha blends over background"
      (colorNear (← shot.readPixel 40 40) 128 0 0)

  -- 4. clip nesting + restore
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      clipRect ⟨0, 0, 20, 20⟩ (drawRect (.solid Color.red) ⟨0, 0⟩ ⟨40, 40⟩)
      -- after the clip body, clipping is restored: this green draws unclipped
      drawRect (.solid Color.green) ⟨25, 25⟩ ⟨20, 20⟩
    let shot ← ren.readPixels
    check "clip: inside-clip pixel drawn" (colorNear (← shot.readPixel 10 10) 255 0 0)
    check "clip: outside-clip pixel untouched" (colorNear (← shot.readPixel 30 5) 0 0 0)
    check "clip: restore lets later draw through" (colorNear (← shot.readPixel 30 30) 0 255 0)

  -- 5. translate composition
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      translate ⟨20, 20⟩ (drawRect (.solid Color.red) ⟨0, 0⟩ ⟨10, 10⟩)
    let shot ← ren.readPixels
    check "translate: shifted region filled" (colorNear (← shot.readPixel 24 24) 255 0 0)
    check "translate: untranslated origin empty" (colorNear (← shot.readPixel 4 4) 0 0 0)

  -- 6. withAlpha scales output alpha (fast-path fill)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      withAlpha 0.5 (drawRect (.solid Color.red) ⟨0, 0⟩ ⟨30, 30⟩)
    let shot ← ren.readPixels
    check "withAlpha: 50% red over black ≈ (128,0,0)"
      (colorNear (← shot.readPixel 10 10) 128 0 0)

  -- 7. linear gradient endpoints ≈ stop colors
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawRect (.linearGradient #[(0, Color.red), (1, Color.blue)] ⟨10, 30⟩ ⟨50, 30⟩)
        ⟨10, 10⟩ ⟨40, 40⟩
    let shot ← ren.readPixels
    check "gradient: left endpoint ≈ red" (colorNear (← shot.readPixel 11 30) 255 0 0 24)
    check "gradient: right endpoint ≈ blue" (colorNear (← shot.readPixel 49 30) 0 0 255 24)
    check "gradient: midpoint ≈ purple" (colorNear (← shot.readPixel 30 30) 128 0 128 12)

  -- 8. elevation shadow fallback (rrShadow tessellation): dark under the
  -- shape, a penumbra just outside the edge, untouched far away
  do
    let ren ← mkRen 128 128
    ren.setDrawColor 255 255 255 255
    ren.clear
    DrawScope.run ren {} do
      drawShape (.rrShadow (RoundRect.ofRect ⟨40, 40, 80, 80⟩) ⟨0, 0⟩ 8 Color.black)
    let shot ← ren.readPixels
    check "shadow: umbra under the shape is dark" (colorNear (← shot.readPixel 60 60) 0 0 0 40)
    let edge ← shot.readPixel 85 60   -- 5 px outside the right edge, σ = 4
    check s!"shadow: penumbra outside the edge is gray (got {showColor edge})"
      (40 < edge.r.toNat && edge.r.toNat < 245)
    check "shadow: far away untouched" (colorNear (← shot.readPixel 120 60) 255 255 255)

  -- 9. layer flatten on SDL: the layer alpha folds into the content, so
  -- self-overlap double-blends — the documented approximation this pins
  -- (the GPU backend composites the layer once instead)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      DrawScope.withLayer ⟨0, 0, 100, 100⟩ 0.5 do
        drawRect (.solid Color.red) ⟨10, 10⟩ ⟨40, 40⟩
        drawRect (.solid Color.red) ⟨30, 10⟩ ⟨40, 40⟩
    let shot ← ren.readPixels
    check "layer flatten: single-covered region ≈ 50% red"
      (colorNear (← shot.readPixel 15 30) 128 0 0)
    check "layer flatten: overlap double-blends to ≈ 75% red (SDL approximation)"
      (colorNear (← shot.readPixel 45 30) 191 0 0)

end Tests.Draw
