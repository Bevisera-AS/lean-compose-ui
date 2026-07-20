import Compose
import ComposeTests.Harness

/-!
# Draw-stack pixel tests (`test/ComposeTests/Draw.lean`)

Headless pixel assertions for `Compose/Ui/Draw/*`. Renders known scenes with the
software renderer under the dummy video driver, reads them back with
`Renderer.readPixels`, and probes individual pixels — the approach lean-sdl3's
own suite proves works headless. Covers: solid/overlapping fills, rounded-rect
corners, circle fill + alpha blend, clip nesting + restore, translate, alpha
scaling, gradient sampling (linear endpoints; radial/sweep on the per-vertex
fallback's near-exact circle-fan cases), the documented SDL layer
approximations (alpha flatten double-blends; blur renders unblurred), and the
shared text run-origin snap (fractional origins render like snapped ones).

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

/-- `RenderBackend.capture` contract: exactly `w × h × 4` bytes, tightly packed
straight-alpha RGBA8 with the top row first — regardless of the backend's
native readback order (the GPU side swizzles its BGRA swapchain into the same
layout; gpu-probe covers that half). This is what `COMPOSE_CAPTURE` streams to
ffmpeg, so a channel-order or stride regression here is a silently wrong GIF. -/
private def backendCapture : IO Unit := do
  let ren ← mkRen 32 16
  let backend ← SdlBackend.create ren
  let (list, _) ← DrawScope.record {} do
    drawRect (.solid Color.red) ⟨0, 0⟩ ⟨16, 16⟩
  let bytes ← backend.capture Color.blue list 32 16
  checkEq "capture: tightly packed, w × h × 4 bytes" bytes.size (32 * 16 * 4)
  let px (x y : Nat) : Array UInt8 :=
    let o := (y * 32 + x) * 4
    #[bytes[o]!, bytes[o + 1]!, bytes[o + 2]!, bytes[o + 3]!]
  -- (4,4) is inside the red rect, (24,4) is bare clear color: both pin the
  -- channel order, and together they pin the row stride and top-down order.
  checkEq "capture: RGBA channel order" (px 4 4) #[255, 0, 0, 255]
  checkEq "capture: clear color fills the rest" (px 24 4) #[0, 0, 255, 255]

/-- Text run-origin snapping (M-j): a run drawn at a fractional origin renders
byte-identically to the same run at the shared `snapTextOrigin` result
(⟨15.4, 20.6⟩ → ⟨15, 21⟩) — the cross-backend invariant whose GPU side
gpu-parity's "text fractional" scene checks. -/
private def textSnap : IO Unit := do
  let ren ← mkRen 160 64
  Sdl.Ttf.init
  let font ← Sdl.Ttf.openFont "assets/fonts/Roboto-Regular.ttf" 16
  let engine ← Sdl.Ttf.createRendererTextEngine ren
  let text ← engine.createText font "The quick brown fox"
  let render (origin : Offset) : IO Sdl.Surface := do
    clearBlack ren
    DrawScope.run ren {} do
      drawText { text, string := "The quick brown fox", color := .white } origin
    ren.readPixels
  let frac ← render ⟨15.4, 20.6⟩
  let snapped ← render ⟨15, 21⟩
  let mut lit := 0
  let mut diffs := 0
  for y in [0:64] do
    for x in [0:160] do
      let a ← frac.readPixel (Int32.ofNat x) (Int32.ofNat y)
      let b ← snapped.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if a.r.toNat > 100 then lit := lit + 1
      if a.r != b.r || a.g != b.g || a.b != b.b then diffs := diffs + 1
  check s!"text snap: glyphs rendered ({lit} lit px)" (lit > 20)
  check s!"text snap: fractional origin matches the snapped rendering ({diffs} diff px)"
    (diffs == 0)

/-- Stretch-layer recording: `withGraphicsLayer (effect := .stretch)` records
exactly one layer prim carrying the intensity; a zero intensity normalizes
away (no layer at all — content records inline). -/
private def stretchRecord : IO Unit := do
  let (list, _) ← DrawScope.record {} do
    DrawScope.withGraphicsLayer ⟨0, 0, 100, 100⟩ {}
      (drawRect (.solid Color.red) ⟨10, 10⟩ ⟨40, 40⟩)
      (effect := .stretch 0 0.5)
  let briefs := list.map (·.brief)
  let expected := s!"layer @(0,0) bounds=(0,0,100,100) a=1 stretch=(0,{fmtF 0.5})\n"
                    ++ "  rect @(0,0) #ff0000ff tl=(10,10) sz=40x40"
  check s!"stretch record: one layer prim carrying the intensity ({briefs})"
    (briefs == #[expected])
  let (flat, _) ← DrawScope.record {} do
    DrawScope.withGraphicsLayer ⟨0, 0, 100, 100⟩ {}
      (drawRect (.solid Color.red) ⟨10, 10⟩ ⟨40, 40⟩)
      (effect := .stretch 0 0)
  check "stretch record: zero intensity records no layer"
    (flat.map (·.brief) == #["rect @(0,0) #ff0000ff tl=(10,10) sz=40x40"])

/-- Backend error hygiene: an IO error while executing primitives must not
leave SDL state stale. A destroyed `Ttf.Text` handle makes its prim throw at
execute time: inside a *transformed layer* the renderer must come back
targeted at the window (not the pooled layer texture, which must also return
to the pool); mid-list the clip must be restored on the way out. Afterwards
the same backend caches render normally. -/
private def errorRestore : IO Unit := do
  let ren ← mkRen 96 96
  Sdl.Ttf.init
  let font ← Sdl.Ttf.openFont "assets/fonts/Roboto-Regular.ttf" 16
  let engine ← Sdl.Ttf.createRendererTextEngine ren
  let text ← engine.createText font "boom"
  text.destroy
  let caches ← SdlBackend.Caches.new
  let badText : Prim := .text { origin := ⟨10, 10⟩ } { text, string := "boom", color := .white }
  -- 1. throw while rendering transformed-layer content
  let badLayer : Prim := .layer {} ⟨0, 0, 40, 40⟩
    { transform := some (.rotation 0.3) } #[badText]
  checkThrows "layer content error propagates" (SdlBackend.execute ren #[badLayer] caches)
  check "renderer target restored after layer content error" (← ren.getTarget).isNone
  -- 2. throw mid-list after a clip was applied
  let clipped : Prim := .rect { clip := some ⟨0, 0, 10, 10⟩ } .red ⟨0, 0⟩ ⟨5, 5⟩
  checkThrows "mid-list error propagates" (SdlBackend.execute ren #[clipped, badText] caches)
  check "clip restored after mid-list error" (!(← ren.clipEnabled))
  -- 3. the backend still renders normally with the same caches
  clearBlack ren
  SdlBackend.execute ren #[.rect {} .red ⟨5, 5⟩ ⟨20, 20⟩] caches
  let shot ← ren.readPixels
  check "backend renders normally after errors" (colorNear (← shot.readPixel 10 10) 255 0 0)

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

  -- 7b. radial + sweep gradients on the per-vertex SDL fallback: a circle fan
  -- centered on the brush center interpolates the radial ramp near-exactly
  -- (center vertex t=0, rim t=1, linear along each spoke); a sweep's rim
  -- colors sit on the rim vertices (interior stays the documented coarse
  -- interpolation — not asserted).
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawCircle (.radial Color.red .blue ⟨40, 40⟩ 30) ⟨40, 40⟩ 30
    let shot ← ren.readPixels
    check "radial: center is the first stop" (colorNear (← shot.readPixel 40 40) 255 0 0 8)
    check "radial: half-radius ≈ midpoint color" (colorNear (← shot.readPixel 55 40) 128 0 128 12)
    check "radial: near the rim ≈ last stop" (colorNear (← shot.readPixel 40 12) 17 0 238 24)
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      drawCircle (.sweepGradient #[(0, Color.red), (1, .blue)] ⟨40, 40⟩) ⟨40, 40⟩ 30
    let shot ← ren.readPixels
    -- Rim samples away from the seam (fan vertices straddling the +x axis
    -- interpolate through it): straight down t = 0.25, left t = 0.5, up
    -- t = 0.75.
    check "sweep: rim straight down ≈ quarter blend"
      (colorNear (← shot.readPixel 40 68) 191 0 64 24)
    check "sweep: rim straight left ≈ half blend"
      (colorNear (← shot.readPixel 12 40) 128 0 128 24)
    check "sweep: rim straight up ≈ three-quarter blend"
      (colorNear (← shot.readPixel 40 12) 64 0 191 24)

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

  -- 10. blur fallback on SDL: `withBlur` content renders *unblurred* — the
  -- documented approximation this pins (the GPU backend runs the separable
  -- Gaussian passes instead, asserted by gpu-probe ⑭): edges stay crisp and
  -- nothing spreads past them.
  do
    let ren ← mkRen 128 128
    clearBlack ren
    DrawScope.run ren {} do
      DrawScope.withBlur ⟨0, 0, 100, 100⟩ 4 do
        drawRect (.solid Color.red) ⟨10, 10⟩ ⟨40, 40⟩
    let shot ← ren.readPixels
    check "blur fallback: content renders solid (unblurred)"
      (colorNear (← shot.readPixel 30 30) 255 0 0)
    check "blur fallback: the edge stays crisp"
      (colorNear (← shot.readPixel 11 30) 255 0 0)
    check "blur fallback: nothing spreads outside"
      (colorNear (← shot.readPixel 54 30) 0 0 0)

  -- 11. stretch-layer recording
  stretchRecord

  -- 12. text run-origin snapping (M-j)
  textSnap

  -- 13. backend error hygiene (target/clip/pool restore across throws)
  errorRestore

  -- 14. RenderBackend.capture readback contract
  backendCapture

end Tests.Draw
