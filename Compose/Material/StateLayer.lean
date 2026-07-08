import Compose.Material.Theme
import Compose.Foundation.Interaction
import Compose.Animation.AnimateAsState

namespace Compose

open Draw

/-!
# Interaction state layers and the bounded ripple (`Compose/Material/StateLayer.lean`)

The shared visual-feedback machinery of every M9 widget, per DESIGN.md's
"state layers instead of full ripple":

- **State layer**: a content-color-tinted overlay over the widget shape whose
  alpha animates (150 ms tween) toward the sum of the Material3 state tokens
  for the currently-raised interaction flags (hover 0.08, focus 0.10, press
  0.10 — Compose composites separate layers; the additive sum is our
  documented approximation).
- **Bounded press ripple**: on press, an expanding circle at the press
  position, geometrically clipped to the widget shape
  (`circleFillClippedToRoundRect` via `DrawScope.clipRoundRect`), radius
  animating 0 → farthest-corner over 300 ms `fastOutSlowIn`; on release the
  circle fades out over 150 ms (radius freezes during the fade — a documented
  simplification of Material's expand-while-fading).

Widgets with a rectangular-ish hit box call `rememberStateLayer` and append
the returned modifier innermost; `Switch`/`Slider` draw a positioned halo
themselves from `rememberStateLayerValues`.

Also here: `rememberUpdatedRef`, the `rememberUpdatedState` analog widgets
use to keep pointer-coroutine callbacks current (the coroutines relaunch on
*key* change only — a freshly-captured `checked` in `onClick` would go stale
otherwise; see `Modifier.clickable`'s docstring).
-/

/-- A remembered cell always holding the latest composed `value`: read it
inside long-lived pointer coroutines/effects instead of capturing composition
values (which freeze at launch). Mirrors
`androidx.compose.runtime.rememberUpdatedState`. -/
def rememberUpdatedRef [Nonempty α] (value : α) : Composable (IO.Ref α) := do
  let r ← remember (IO.mkRef value)
  r.set value
  return r

/-- Target state-layer alpha for the raised interaction flags: the additive
sum of the Material3 hover/focus/press tokens (see the module docstring). -/
def stateLayerTargetAlpha (hovered focused pressed : Bool) : Float32 :=
  (if hovered then stateLayerHoverAlpha else 0)
    + (if focused then stateLayerFocusAlpha else 0)
    + (if pressed then stateLayerPressAlpha else 0)

#guard stateLayerTargetAlpha false false false == 0
#guard stateLayerTargetAlpha true false false == stateLayerHoverAlpha
#guard stateLayerTargetAlpha false true false == stateLayerFocusAlpha
#guard stateLayerTargetAlpha true true true
        == stateLayerHoverAlpha + stateLayerFocusAlpha + stateLayerPressAlpha

/-- Distance from `p` to the farthest corner of `r` — the ripple radius that
covers the whole shape from the press position. Mirrors
`RippleAnimation`'s end-radius computation. -/
def coverRadius (r : Rect) (p : Offset) : Float32 :=
  max (max (p.distance r.topLeft) (p.distance ⟨r.right, r.top⟩))
      (max (p.distance ⟨r.left, r.bottom⟩) (p.distance ⟨r.right, r.bottom⟩))

#guard coverRadius ⟨0, 0, 30, 40⟩ ⟨0, 0⟩ == 50      -- to the far corner
#guard coverRadius ⟨0, 0, 30, 40⟩ ⟨30, 40⟩ == 50
#guard coverRadius ⟨0, 0, 20, 0⟩ ⟨5, 0⟩ == 15
#guard coverRadius ⟨0, 0, 10, 10⟩ ⟨5, 5⟩ == (50 : Float32).sqrt

/-- The animated interaction feedback of one widget, sampled at composition
time (the containing scope recomposes per animation frame — the framework's
established `animate*AsState` consumption pattern). -/
structure StateLayerValues where
  /-- Current overlay alpha (hover/focus/press layers). -/
  layerAlpha : Float32
  /-- Current ripple opacity (`0` = no ripple visible). -/
  rippleAlpha : Float32
  /-- Ripple expansion fraction in `[0, 1]` of the cover radius. -/
  rippleProgress : Float32
  /-- Latest press position, local to the widget's pointer region (px). -/
  pressCenter : IO.Ref Offset

/-- Remembered ripple animation state (radius fraction + opacity). -/
private structure RippleAnim where
  progress : Animatable Float32
  alpha : Animatable Float32

private instance : Nonempty RippleAnim :=
  ⟨{ progress := Classical.choice inferInstance, alpha := Classical.choice inferInstance }⟩

private def RippleAnim.create : IO RippleAnim :=
  return { progress := ← Animatable.create 0 .float32
           alpha := ← Animatable.create 0 .float32 }

/-- Record press positions into `center` without consuming anything: appended
*innermost*, it sees each press before `clickable`'s detector consumes it
(dispatch is innermost-element-first within a node). -/
private partial def recordPresses (center : IO.Ref Offset)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then center.set ev.position
  recordPresses center scope

/-- Track `source`'s flags and animate the shared feedback values: overlay
alpha tweens (150 ms) to the state-token sum; a rising press launches the
ripple (expand 300 ms `fastOutSlowIn`), a falling one fades it (150 ms).
Widgets drawing their own halo (`Switch`, `Slider`) consume this directly;
everything else uses `rememberStateLayer`. -/
def rememberStateLayerValues (source : InteractionSource) :
    Composable StateLayerValues := do
  let hovered ← source.hovered.get
  let focused ← source.focused.get
  let pressed ← source.pressed.get
  let layerAlpha ← animateFloatAsState (stateLayerTargetAlpha hovered focused pressed)
    (.tween 150 0 .fastOutSlowIn)
  let ripple ← remember RippleAnim.create
  let pressCenter ← remember (IO.mkRef Offset.zero)
  LaunchedEffect pressed do
    if pressed then
      ripple.progress.snapTo 0
      ripple.alpha.snapTo stateLayerPressAlpha
      ripple.progress.animateTo 1 (.tween 300 0 .fastOutSlowIn)
    else
      unless (← ripple.alpha.peek) == 0 do
        ripple.alpha.animateTo 0 (.tween 150 0 .linear)
  return { layerAlpha := ← layerAlpha.get
           rippleAlpha := ← ripple.alpha.value.get
           rippleProgress := ← ripple.progress.value.get
           pressCenter }

/-- Draw the overlay + bounded ripple over the widget's `shape` in `tint`
(sampled `values`). Runs in the widget's `drawBehind` coordinates. -/
def drawStateLayer (values : StateLayerValues) (shape : Shape) (tint : Color) :
    DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let rr := shape.toRoundRect sz ctx.density
  if values.layerAlpha > 0.001 then
    DrawScope.drawRoundRect (.solid (tint.withAlpha values.layerAlpha)) rr
  if values.rippleAlpha > 0.001 && values.rippleProgress > 0 then
    let c ← values.pressCenter.get
    DrawScope.clipRoundRect rr <|
      DrawScope.drawCircle (.solid (tint.withAlpha values.rippleAlpha)) c
        (coverRadius rr.rect c * values.rippleProgress)

/-- The full state-layer package as a modifier: append it **innermost**
(after `clickable` and any background) so its press recorder sees events
first and its overlay draws over the container but under content. The tint
defaults to the ambient `LocalContentColor`. When `enabled` is false the
returned modifier is empty (disabled widgets show no interaction feedback).
Mirrors the `indication`/ripple half of `androidx.compose.material3`'s
interactive components. -/
def rememberStateLayer (source : InteractionSource) (shape : Shape)
    (tint : Option Color := none) (enabled : Bool := true) : Composable Modifier := do
  let values ← rememberStateLayerValues source
  let tint ← match tint with
    | some t => pure t
    | none => LocalContentColor.current
  if enabled then
    return Modifier.pointerInput
        (mixKeys (stringKey "Compose.Material.stateLayer") source.id)
        (recordPresses values.pressCenter)
      |>.drawBehind (drawStateLayer values shape tint)
  else
    return {}

end Compose
