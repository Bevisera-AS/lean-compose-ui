import Compose.Material.Theme
import Compose.Foundation.Scroll
import Compose.Foundation.Interaction
import Compose.Animation.AnimateAsState

namespace Compose

open Draw

/-!
# Desktop scrollbar (`Compose/Material/Scrollbar.lean`)

`VerticalScrollbar` — the desktop companion of a scroll container, mirroring
Compose-for-Desktop's `VerticalScrollbar`/`rememberScrollbarAdapter` on the
M10 diet: place it in a `Box` over the scrolling content (e.g.
`BoxScope.align .centerEnd` + `Modifier.fillMaxHeight`).

* Proportional draggable thumb (min `24.dp`), colored `onSurface` at low
  alpha; dragging maps 1:1 through the track↔content ratio.
* Track clicks page by one viewport toward the click.
* Auto-hide: visible while the pointer hovers it or within ~1 s of scroll
  activity (a `LaunchedEffect` keyed on the scroll value — pure scheduler
  time, testable with a fake clock), fading via `animateFloatAsState`.
* Hover widens the thumb 4 dp → 8 dp (animated); the hit strip stays 8 dp.
-/

/-- Minimum thumb length. -/
def scrollbarMinThumb : Dp := 24

/-- Idle milliseconds before the scrollbar fades out. -/
def scrollbarHideDelayMs : UInt32 := 1000

/-- Thumb geometry inside a `track`-px strip: `(length, offset)`. The length
is proportional (`track × viewport / content`, floored at `minThumb` and
capped at the track); the offset maps `value / maxValue` onto the leftover
travel. A non-scrollable container gets a full-track thumb at `0`. -/
def scrollbarThumb (track viewport content value minThumb : Float32) :
    Float32 × Float32 :=
  if content ≤ viewport || track ≤ 0 || viewport ≤ 0 then (track, 0) else
  let len := min (max (track * viewport / content) minThumb) track
  let maxVal := content - viewport
  let f := min (max (value / maxVal) 0) 1
  (len, (track - len) * f)

#guard scrollbarThumb 100 50 200 0 24 == (25, 0)
#guard scrollbarThumb 100 50 200 150 24 == (25, 75)     -- at max: bottom
#guard scrollbarThumb 100 50 200 75 24 == (25, 37.5)    -- half way
#guard scrollbarThumb 100 50 1000 0 24 == (24, 0)       -- min-thumb floor
#guard scrollbarThumb 100 50 40 0 24 == (100, 0)        -- not scrollable
#guard scrollbarThumb 100 50 200 999 24 == (25, 75)     -- value over-clamp

/-- The scrollbar's pointer coroutine: a press on the thumb starts a drag
(1:1 through the travel↔scroll ratio, from the value at press); a press on
the track pages one viewport toward the click. -/
private partial def scrollbarGesture (state : ScrollState)
    (minThumbPx : Float32) (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    let track := (← scope.size).height.toFloat32
    let viewport ← state.viewportSizeState.cell.get
    let content ← state.contentSizeState.cell.get
    let maxVal ← state.maxValueState.cell.get
    let v0 ← state.valueState.cell.get
    let (len, off) := scrollbarThumb track viewport content v0 minThumbPx
    if off ≤ ev.position.y && ev.position.y < off + len then
      -- Thumb drag: track-px travel maps onto the scrollable range.
      let travel := track - len
      let ratio := if travel ≤ 0 then 0 else maxVal / travel
      drag ev.position.y v0 ratio
    else
      -- Track click: page toward the click.
      let _ ← state.scrollBy (if ev.position.y < off then -viewport else viewport)
  scrollbarGesture state minThumbPx scope
where
  /-- Follow one thumb drag until release/window-leave. -/
  drag (y0 v0 ratio : Float32) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      ev.consume
      state.scrollTo (v0 + (ev.position.y - y0) * ratio)
      drag y0 v0 ratio
    | .release => ev.consume
    | .exit => pure ()
    | _ => drag y0 v0 ratio

/-- A desktop-style vertical scrollbar for `state`'s scroll container (see
the module docstring). Overlay-style: give it a height (e.g.
`Modifier.fillMaxHeight`) and align it over the content's end edge; it is
8 dp wide. Mirrors `androidx.compose.foundation.VerticalScrollbar`
(Compose for Desktop). -/
composable def VerticalScrollbar (state : ScrollState)
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let density ← LocalDensity.current
  let source ← rememberInteractionSource
  let hovered ← source.hovered.get
  -- Scroll activity: any value change shows the bar and restarts the hide
  -- timer (the LaunchedEffect relaunches on the changed key).
  let value ← state.value
  let active ← remember (mutableStateOf true)
  LaunchedEffect value do
    active.set true
    UiTask.delay scrollbarHideDelayMs
    active.set false
  let isActive ← active.get
  let alphaState ← animateFloatAsState (if hovered || isActive then 1.0 else 0.0)
    (.tween 200 0 .linear)
  let widthState ← animateDpAsState (if hovered then 8 else 4) (.tween 120 0 .linear)
  let alpha ← alphaState.get
  let thumbW ← widthState.get
  let viewport ← state.viewportSize
  let content ← state.contentSize
  let minThumbPx := density.dpToPx scrollbarMinThumb
  let m := modifier
    |>.width 8
    |>.hoverable source
    |>.pointerInput (mixKeys (stringKey "Compose.Material.VerticalScrollbar") state.id)
        (scrollbarGesture state minThumbPx)
    |>.drawBehind do
      let sz ← DrawScope.size
      if alpha > 0.001 && content > viewport then
        let (len, off) := scrollbarThumb sz.height viewport content value minThumbPx
        -- Track (subtle, hover only) + right-aligned thumb.
        if hovered then
          DrawScope.drawRect (.solid (colors.onSurface.withAlpha (0.06 * alpha)))
            .zero sz
        let wpx := density.dpToPx thumbW
        DrawScope.drawRoundRect
          (.solid (colors.onSurface.withAlpha (0.4 * alpha)))
          (RoundRect.circular ⟨sz.width - wpx, off, sz.width, off + len⟩ (wpx / 2))
  Layout m .leaf (policyInputs := some 0x73626172)

end Compose
