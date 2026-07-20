module

public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout

public section

namespace Compose

open Draw

/-!
# Slider (`Compose/Material/Slider.lean`)

The M9 input workhorse: a 4 dp track (active `primary` / inactive
`surfaceVariant`) with a 10 dp-radius thumb, 40 dp tall, filling the
available width (min 144 dp). Interaction, mirroring
`androidx.compose.material3.Slider`:

- **press-to-seek**: a press anywhere on the track jumps the value there and
  starts a drag;
- **drag**: every move updates the value continuously; release (or window
  leave) fires `onValueChangeFinished`;
- **keyboard**: Left/Right step (one tick with `steps`, 1 % of the range
  otherwise; repeats allowed), Home/End jump to the ends, all firing
  `onValueChangeFinished` — when focused (Tab reaches it);
- **steps**: `steps` evenly spaced intermediate stops; values snap to the
  grid and tick dots are drawn on the track;
- **halo**: a 20 dp hover/focus/press state layer behind the thumb.

The value is a controlled prop: the pointer coroutine reads its callbacks,
range, and steps through a `rememberUpdatedRef` cell so it never goes stale
(it relaunches on `enabled`/identity changes only).
-/

/-- Clamp to `[0, 1]`. -/
private def clamp01 (x : Float32) : Float32 := min 1 (max 0 x)

/-- Snap a track fraction to the `steps` grid (`steps` intermediate stops ⇒
`steps + 1` equal intervals); `steps = 0` is continuous. Mirrors the
step-snapping of `SliderState`. -/
def snapFraction (f : Float32) (steps : Nat) : Float32 :=
  if steps == 0 then clamp01 f
  else
    let n := (steps + 1).toFloat32
    (clamp01 f * n + 0.5).floor / n

#guard snapFraction 0.42 0 == 0.42
#guard snapFraction 1.2 0 == 1.0
#guard snapFraction 0.42 3 == 0.5    -- grid 0, ¼, ½, ¾, 1
#guard snapFraction 0.1 3 == 0.0
#guard snapFraction 0.13 3 == 0.25
#guard snapFraction 1.0 3 == 1.0
#guard snapFraction 0.55 1 == 0.5    -- grid 0, ½, 1

/-- Track fraction of `x` px on a `width`-px slider with `pad`-px end
insets, snapped to `steps`. -/
def sliderFractionAt (width pad x : Float32) (steps : Nat) : Float32 :=
  snapFraction ((x - pad) / max 1 (width - 2 * pad)) steps

#guard sliderFractionAt 220 10 110 0 == 0.5
#guard sliderFractionAt 220 10 10 0 == 0.0
#guard sliderFractionAt 220 10 500 0 == 1.0    -- clamped
#guard sliderFractionAt 220 10 90 3 == 0.5     -- 0.4 snaps up to ½

/-- Map a fraction into `range` (lo, hi). -/
private def lerpRange (range : Float32 × Float32) (f : Float32) : Float32 :=
  range.1 + f * (range.2 - range.1)

/-- The live parameters the pointer coroutine reads per event (kept current
by `rememberUpdatedRef` — see the module docstring). -/
private structure SliderParams where
  onChange : Float32 → IO Unit
  onFinished : IO Unit
  range : Float32 × Float32
  steps : Nat
  density : Density
  /-- Optimistic latest reported value (the TextField pattern): events
  landing between two recompositions — key repeat, seek + key in one frame
  drain — step from here instead of the stale composition capture;
  recomposition re-syncs it with the authoritative `value` prop. -/
  latest : IO.Ref Float32

private instance : Nonempty SliderParams :=
  ⟨{ onChange := fun _ => pure (), onFinished := pure (), range := (0, 1)
     steps := 0, density := {}, latest := Classical.choice inferInstance }⟩

/-- End inset of the track: the thumb radius plus a hair, in dp. -/
private def trackPad : Dp := 12

/-- The press-seek + drag gesture (see the module docstring). Presses and
drag moves are consumed; `pressed` drives the halo. -/
private partial def sliderGesture (params : IO.Ref SliderParams)
    (source : InteractionSource) (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    source.pressed.set true
    seek ev.position
    dragLoop
  sliderGesture params source scope
where
  /-- Update the value from an event position. -/
  seek (pos : Offset) : UiTask Unit := do
    let p ← params.get
    let sz ← scope.size
    let pad := p.density.dpToPx trackPad
    let f := sliderFractionAt sz.width.toFloat32 pad pos.x p.steps
    let v := lerpRange p.range f
    p.latest.set v
    p.onChange v
  /-- Follow the press until release/window-leave. -/
  dragLoop : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      ev.consume
      seek ev.position
      dragLoop
    | .release =>
      ev.consume
      source.pressed.set false
      (← params.get).onFinished
    | .exit =>
      source.pressed.set false
      (← params.get).onFinished
    | _ => dragLoop

/-- Draw the track (active/inactive), step ticks, thumb halo, and thumb.
`fraction` is the current value's track fraction. -/
private def drawSlider (fraction : Float32) (steps : Nat)
    (active inactive activeTick inactiveTick halo : Color)
    (haloAlpha : Float32) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let px (d : Dp) : Float32 := ctx.density.dpToPx d
  let pad := px trackPad
  let cy := sz.height / 2
  let x0 := pad
  let x1 := sz.width - pad
  let tx := x0 + fraction * (x1 - x0)
  let th := px 4
  let band (l r : Float32) (c : Color) : DrawM Unit :=
    if r - l > 0.5 then
      DrawScope.drawRoundRect (.solid c)
        (RoundRect.circular ⟨l, cy - th / 2, r, cy + th / 2⟩ (th / 2))
    else pure ()
  band x0 tx active
  band tx x1 inactive
  -- Tick dots on the snap grid.
  if steps > 0 then
    for i in [0:steps + 2] do
      let f := i.toFloat32 / (steps + 1).toFloat32
      let x := x0 + f * (x1 - x0)
      DrawScope.drawCircle (.solid (if f ≤ fraction then activeTick else inactiveTick))
        ⟨x, cy⟩ (px 1.5)
  if haloAlpha > 0.001 then
    DrawScope.drawCircle (.solid (halo.withAlpha haloAlpha)) ⟨tx, cy⟩ (px 20)
  DrawScope.drawCircle (.solid active) ⟨tx, cy⟩ (px 10)

/-- A Material slider (see the module docstring). `value` is a controlled
prop: `onValueChange` fires continuously during seek/drag/keying and
`onValueChangeFinished` when an interaction completes. Mirrors
`androidx.compose.material3.Slider`. -/
composable def Slider (value : Float32) (onValueChange : Float32 → IO Unit)
    (modifier : Modifier := {}) (valueRange : Float32 × Float32 := (0, 1))
    (steps : Nat := 0) (enabled : Bool := true)
    (onValueChangeFinished : IO Unit := pure ()) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let density ← LocalDensity.current
  let source ← rememberInteractionSource
  -- Optimistic latest-value ref (the TextField pattern): re-synced with the
  -- authoritative prop every recomposition; all reported changes go through
  -- it so back-to-back events in one frame drain compose.
  let valueRef ← remember (IO.mkRef value)
  valueRef.set value
  let params ← rememberUpdatedRef
    ({ onChange := onValueChange, onFinished := onValueChangeFinished
       range := valueRange, steps, density, latest := valueRef } : SliderParams)
  let values ← rememberStateLayerValues source
  let span := valueRange.2 - valueRange.1
  let fraction := snapFraction (if span == 0 then 0 else (value - valueRange.1) / span) steps
  -- Keyboard: step from the optimistic ref, not the composition-captured
  -- `value` — two key repeats landing in one frame drain must each take a
  -- step (the second would otherwise recompute from the stale capture).
  let keyStep : Float32 := if steps > 0 then span / (steps + 1).toFloat32 else span / 100
  let onKey (ke : KeyEvent) : IO Bool := do
    if !enabled || !ke.down then return false
    let v ← valueRef.get
    let target : Option Float32 :=
      if ke.key == .left then some (max valueRange.1 (v - keyStep))
      else if ke.key == .right then some (min valueRange.2 (v + keyStep))
      else if ke.key == .home then some valueRange.1
      else if ke.key == .«end» then some valueRange.2
      else none
    match target with
    | some v' =>
      valueRef.set v'
      let p ← params.get
      p.onChange v'
      p.onFinished
      return true
    | none => return false
  let active := if enabled then colors.primary
                else colors.onSurface.withAlpha disabledContentAlpha
  let inactive := if enabled then colors.surfaceVariant
                  else colors.onSurface.withAlpha disabledContainerAlpha
  let haloAlpha := if enabled then values.layerAlpha else 0
  let m := modifier
    |>.height 40
    |>.fillMaxWidth
    |>.sizeIn (minWidth := some 144)
    |>.semantics (role := some .slider) (disabled := some !enabled)
        (range := some { current := value, min := valueRange.1
                         max := valueRange.2, steps })
    |>.hoverable source enabled
    |>.focusable enabled
    |>.onFocusChanged source.focused.set
    |>.onKeyEvent onKey
    |>.pointerInput
        (mixKeys (stringKey "Compose.Material.Slider")
          (mixKeys source.id (if enabled then 1 else 0)))
        (if enabled then sliderGesture params source else fun _ => pure ())
    |>.drawBehind (drawSlider fraction steps active inactive
        colors.onPrimary colors.onSurfaceVariant colors.primary haloAlpha)
  Layout m .leaf

end Compose

end
