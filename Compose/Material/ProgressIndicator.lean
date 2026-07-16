module

public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout
public import Compose.Animation.Transition
public meta import Compose.Animation.Transition

public section

namespace Compose

open Draw

/-!
# Progress indicators (`Compose/Material/ProgressIndicator.lean`)

`LinearProgressIndicator` (a 4 dp rounded bar, 240 dp default width) and
`CircularProgressIndicator` (a 40 dp, 4 dp-stroke arc), each in two modes
per their `androidx.compose.material3` namesakes:

- **determinate** (`progress = some f`): the bar/arc covers fraction `f`
  (clamped) in `primary` over a `surfaceVariant` track (the circular
  indicator draws no track, like M3);
- **indeterminate** (`progress = none`): the linear bar runs Material's
  two-segment head/tail choreography — two `primary` bars, each spanning
  `[tail, head]` of the width, with the tail lagging the head on staggered
  cubic easings over an 1800 ms cycle (`linearIndeterminateBars`); the
  circular indicator spins an arc whose length breathes between 10 % and
  75 % of the circle while it rotates.

Semantics: the determinate mode publishes a `ProgressBarRangeInfo` (`Range`);
the indeterminate mode publishes the `progressBar` role with **no** range
(mirroring M3's `ProgressBarRangeInfo.Indeterminate`) — the `progress.map`
below yields `none` exactly when indeterminate.
-/

/-- π as `Float32`. -/
private def piF : Float32 := 3.14159265358979323846

/-- Clamp to `[0, 1]`. -/
private def clamp01 (x : Float32) : Float32 := min 1 (max 0 x)

/-! ## Linear indeterminate choreography (Material's two head/tail segments)

Each of the four fractions animates `0 → 1` over the 1800 ms cycle on its own
staggered, cubic-eased keyframe curve; a bar spans `[tail, head]` of the
track width. The constants and easings mirror
`androidx.compose.material3.ProgressIndicator`'s
`FirstLine*`/`SecondLine*` timings. -/

/-- `head₁` curve: rises `0→1` over `[0, 750]` ms, then holds. -/
private def firstHeadSpec : AnimationSpec Float32 :=
  .keyframes 1800 [(0, 0, Easing.cubicBezier 0.2 0 0.8 1), (750, 1, .linear)]
/-- `tail₁` curve: holds until 333 ms, rises `0→1` over `[333, 1183]`, holds. -/
private def firstTailSpec : AnimationSpec Float32 :=
  .keyframes 1800 [(0, 0, .linear), (333, 0, Easing.cubicBezier 0.4 0 1 1), (1183, 1, .linear)]
/-- `head₂` curve: holds until 1000 ms, rises `0→1` over `[1000, 1567]`, holds. -/
private def secondHeadSpec : AnimationSpec Float32 :=
  .keyframes 1800 [(0, 0, .linear), (1000, 0, Easing.cubicBezier 0 0 0.65 1), (1567, 1, .linear)]
/-- `tail₂` curve: holds until 1267 ms, rises `0→1` over `[1267, 1800]`. -/
private def secondTailSpec : AnimationSpec Float32 :=
  .keyframes 1800 [(0, 0, .linear), (1267, 0, Easing.cubicBezier 0.1 0 0.45 1), (1800, 1, .linear)]

/-- The two indeterminate bars `((tail₁, head₁), (tail₂, head₂))` as width
fractions at `ms` into the 1800 ms cycle. Pure — the choreography sampled for
tests. -/
def linearIndeterminateBars (ms : Nat) : (Float32 × Float32) × (Float32 × Float32) :=
  let sample (spec : AnimationSpec Float32) : Float32 :=
    (spec.valueAt .float32 (AnimationSpec.msToNs ms) (.v1 0) (.v1 1) (.v1 0)).get 0
  ((sample firstTailSpec, sample firstHeadSpec), (sample secondTailSpec, sample secondHeadSpec))

-- At the cycle start nothing is drawn; the head always leads (≥) its tail.
#guard (linearIndeterminateBars 0).1 == (0, 0)
#guard (linearIndeterminateBars 0).2 == (0, 0)
-- Early on the first head has grown while its tail still lags at 0 (t < 333).
#guard let ((t1, h1), _) := linearIndeterminateBars 300; h1 > 0.1 && t1 == 0 && h1 ≥ t1
-- By 900 ms the first head has fully swept; its tail is climbing behind it.
#guard let ((t1, h1), _) := linearIndeterminateBars 900; h1 == 1 && t1 > 0 && h1 ≥ t1
-- Late in the cycle the second bar is active, head still ≥ tail.
#guard let (_, (t2, h2)) := linearIndeterminateBars 1400; h2 > 0 && h2 ≥ t2

/-- Draw one rounded track band from fraction `f0` to `f1`. -/
private def drawBand (f0 f1 : Float32) (c : Color) : DrawM Unit := do
  let sz ← DrawScope.size
  let l := f0 * sz.width
  let r := f1 * sz.width
  if r - l > 0.5 then
    DrawScope.drawRoundRect (.solid c)
      (RoundRect.circular ⟨l, 0, r, sz.height⟩ (sz.height / 2))

/-- A horizontal progress bar (see the module docstring). Mirrors
`androidx.compose.material3.LinearProgressIndicator`. -/
composable def LinearProgressIndicator (progress : Option Float32 := none)
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let m := modifier
    |>.semantics (role := some .progressBar)
        (range := progress.map fun f => { current := clamp01 f })
    |>.sizeIn (minWidth := some 240) |>.height 4
  match progress with
  | some f =>
    let f := clamp01 f
    Layout (m.drawBehind do
      drawBand 0 1 colors.surfaceVariant
      drawBand 0 f colors.primary) .leaf
  | none =>
    -- Two-segment head/tail dance: four staggered keyframe curves, each a
    -- separate infinite property, span two `primary` bars over the track.
    let it ← rememberInfiniteTransition
    let firstHead ← it.animateFloat 0 1 (.infiniteRepeatable firstHeadSpec)
    let firstTail ← it.animateFloat 0 1 (.infiniteRepeatable firstTailSpec)
    let secondHead ← it.animateFloat 0 1 (.infiniteRepeatable secondHeadSpec)
    let secondTail ← it.animateFloat 0 1 (.infiniteRepeatable secondTailSpec)
    let (fh, ft) := (← firstHead.get, ← firstTail.get)
    let (sh, st) := (← secondHead.get, ← secondTail.get)
    Layout (m.drawBehind do
      drawBand 0 1 colors.surfaceVariant
      drawBand ft fh colors.primary
      drawBand st sh colors.primary) .leaf

/-- A circular progress arc (see the module docstring). Mirrors
`androidx.compose.material3.CircularProgressIndicator`. -/
composable def CircularProgressIndicator (progress : Option Float32 := none)
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let m := modifier
    |>.semantics (role := some .progressBar)
        (range := progress.map fun f => { current := clamp01 f })
    |>.size 40 40
  let arc (startRad sweepRad : Float32) : DrawM Unit := do
    let ctx ← read
    let sz ← DrawScope.size
    if sweepRad > 0.001 then
      DrawScope.drawArc (.solid colors.primary) sz.center
        (min sz.width sz.height / 2 - ctx.density.dpToPx 2) startRad sweepRad
        (ctx.density.dpToPx 4)
  match progress with
  | some f =>
    let f := clamp01 f
    Layout (m.drawBehind (arc (-piF / 2) (f * 2 * piF))) .leaf
  | none =>
    let it ← rememberInfiniteTransition
    -- Rotation spins one turn per 1332 ms; the arc length breathes between
    -- 10 % and 75 % of the circle on a reversing 666 ms tween.
    let rot ← it.animateFloat 0 (2 * piF)
      (.infiniteRepeatable (.tween 1332 0 .linear))
    let len ← it.animateFloat (0.1 * 2 * piF) (0.75 * 2 * piF)
      (.infiniteRepeatable (.tween 666 0 .fastOutSlowIn) .reverse)
    let startRad := (← rot.get) - piF / 2
    Layout (m.drawBehind (arc startRad (← len.get))) .leaf

end Compose

end
