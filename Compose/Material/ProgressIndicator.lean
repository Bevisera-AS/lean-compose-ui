import Compose.Material.Theme
import Compose.Material.StateLayer
import Compose.Ui.Layout
import Compose.Animation.Transition

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
- **indeterminate** (`progress = none`): an `InfiniteTransition` drives a
  sweeping 30 %-wide bar segment (1.2 s cycle), or a spinning arc whose
  length oscillates between 10 % and 75 % of the circle while rotating
  (a simplified take on M3's four-phase choreography).
-/

/-- π as `Float32`. -/
private def piF : Float32 := 3.14159265358979323846

/-- Clamp to `[0, 1]`. -/
private def clamp01 (x : Float32) : Float32 := min 1 (max 0 x)

/-- The linear indicator's bar segment for animation time `t ∈ [0, 1)`: a
0.3-wide window sweeping from fully-left-of-track to fully-right, clamped to
`[0, 1]`. Returned as (start, end) fractions. -/
def linearSweepSegment (t : Float32) : Float32 × Float32 :=
  let head := t * 1.3
  (clamp01 (head - 0.3), clamp01 head)

/-- Componentwise `|·| ≤ 1e-6` comparison for the guards (Float32 rounding). -/
private def segNear (a b : Float32 × Float32) : Bool :=
  (a.1 - b.1).abs ≤ 1e-6 && (a.2 - b.2).abs ≤ 1e-6

#guard segNear (linearSweepSegment 0) (0, 0)
#guard segNear (linearSweepSegment 0.5) (0.35, 0.65)
#guard segNear (linearSweepSegment 1) (1, 1)

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
    let it ← rememberInfiniteTransition
    let t ← it.animateFloat 0 1 (.infiniteRepeatable (.tween 1200 0 .fastOutSlowIn))
    let (s, e) := linearSweepSegment (← t.get)
    Layout (m.drawBehind do
      drawBand 0 1 colors.surfaceVariant
      drawBand s e colors.primary) .leaf

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
