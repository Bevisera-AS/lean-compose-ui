module

public import Compose.Core.Density
public meta import Compose.Core.Density

public section

namespace Compose

/-!
# Android spline fling decay (`Compose/Animation/SplineDecay.lean`)

The deceleration curve Android scrolling actually uses, ported from
androidx `SplineBasedDecay.kt` (`AndroidFlingSpline`) and
`FlingCalculator.kt`, which themselves mirror AOSP
`OverScroller.SplineOverScroller`. Compared to `ExponentialDecay` the
spline coasts farther on fast flings and eases out with the
characteristic Android tail — this is most of "feels like Android".

The model: a fling's total distance and duration are closed forms of the
initial velocity (via the "spline deceleration" exponent `l`), and the
position over normalized time follows a sampled Bézier-derived spline
(`splinePositions`); velocities read off the same table's slopes.

Consumed by `ScrollState.fling` via `SplineDecay.spec`
(`Compose/Animation/Decay.lean`); everything here is pure and
`#guard`-tested.
-/

/-- AOSP fling deceleration exponent `ln 0.78 / ln 0.9` (≈ 2.358):
each 10% speed loss covers 22% less ground. -/
def decelerationRate : Float := Float.log 0.78 / Float.log 0.9

#guard (decelerationRate - 2.3582017).abs < 1e-4

namespace SplineDecay

/-- The fraction of a fling's duration spent covering the "ballistic"
first stretch; also the spline's initial slope is `1/inflection`
(AOSP `INFLEXION`). -/
private def inflection : Float := 0.35

private def startTension : Float := 0.5
private def endTension : Float := 1.0
private def p1 : Float := startTension * inflection
private def p2 : Float := 1.0 - endTension * (1.0 - inflection)

/-- Spline sample count (AOSP `NB_SAMPLES`). -/
private def nbSamples : Nat := 100

/-- The sampled fling spline: `(positions, times)`, each `nbSamples + 1`
entries. Entry `i` of `positions` is the distance fraction covered at
normalized time `i/100` (and `times` the transpose), found by bisecting
the Bézier parameter until the complementary coordinate hits `i/100`
(tolerance 1e-5). `xMin`/`yMin` persist across samples exactly as in
AOSP (the parameter is monotone in the sample index). The unbounded
`while true` searches become fueled loops (64 halvings from an interval
of width 1 — convergence needs ~20) so the definition stays total and
`#guard`-evaluable. -/
private def splineTables : Array Float × Array Float := Id.run do
  let mut positions : Array Float := Array.emptyWithCapacity (nbSamples + 1)
  let mut times : Array Float := Array.emptyWithCapacity (nbSamples + 1)
  let mut xMin : Float := 0.0
  let mut yMin : Float := 0.0
  for i in [0:nbSamples] do
    let alpha := i.toFloat / nbSamples.toFloat
    let mut xMax : Float := 1.0
    let mut x := xMin
    for _ in [0:64] do
      x := xMin + (xMax - xMin) / 2.0
      let tx := 3.0 * x * (1.0 - x) * ((1.0 - x) * p1 + x * p2) + x * x * x
      if (tx - alpha).abs < 1e-5 then break
      if tx > alpha then xMax := x else xMin := x
    positions := positions.push
      (3.0 * x * (1.0 - x) * ((1.0 - x) * startTension + x) + x * x * x)
    let mut yMax : Float := 1.0
    let mut y := yMin
    for _ in [0:64] do
      y := yMin + (yMax - yMin) / 2.0
      let dy := 3.0 * y * (1.0 - y) * ((1.0 - y) * startTension + y) + y * y * y
      if (dy - alpha).abs < 1e-5 then break
      if dy > alpha then yMax := y else yMin := y
    times := times.push
      (3.0 * y * (1.0 - y) * ((1.0 - y) * p1 + y * p2) + y * y * y)
  positions := positions.push 1.0
  times := times.push 1.0
  return (positions, times)

-- Both tables run 0 → 1 (the first entry is the bisection's ~1e-5-sized
-- hit for alpha = 0, not exactly zero) and are monotone.
#guard splineTables.1.size == 101 && splineTables.2.size == 101
#guard splineTables.1[0]!.abs < 1e-4 && splineTables.2[0]!.abs < 1e-4
#guard splineTables.1[100]! == 1.0 && splineTables.2[100]! == 1.0
#guard (Array.range 100).all fun i => splineTables.1[i]! ≤ splineTables.1[i+1]!
#guard (Array.range 100).all fun i => splineTables.2[i]! ≤ splineTables.2[i+1]!
-- The spline's initial slope is 1/inflection ≈ 2.857 (distance fraction
-- outruns time fraction by exactly the INFLEXION ratio at launch).
#guard (splineTables.1[1]! * 100.0 - 1.0 / 0.35).abs < 0.1

/-- Distance and velocity coefficients at normalized time `t`
(AOSP `flingPosition`): linear interpolation between spline samples,
`(1, 0)` once past the end. -/
def flingPosition (t : Float) : Float × Float :=
  let positions := splineTables.1
  let index := (max t 0.0 * nbSamples.toFloat).toUInt64.toNat
  if index < nbSamples then
    let tInf := index.toFloat / nbSamples.toFloat
    let tSup := (index + 1).toFloat / nbSamples.toFloat
    let dInf := positions[index]!
    let dSup := positions[index + 1]!
    let velocityCoef := (dSup - dInf) / (tSup - tInf)
    (dInf + (t - tInf) * velocityCoef, velocityCoef)
  else (1.0, 0.0)

#guard flingPosition 1.0 == (1.0, 0.0)
#guard flingPosition 2.0 == (1.0, 0.0)
#guard (flingPosition 0.0).1.abs < 1e-4

end SplineDecay

/-- Android's fling physics. `friction` is AOSP
`ViewConfiguration.SCROLL_FRICTION`; `density` is the display's px/dp
scale (px-per-inch = 160·density, the mdpi baseline) — pass the real
density on device or the curve plays at the wrong physical speed. The
fling ends when the speed falls under `absVelocityThreshold` (px/s;
androidx uses 0 — we keep `ExponentialDecay`'s 1 px/s floor so the
duration formula never sees a vanishing velocity). -/
structure SplineDecay where
  friction : Float32 := 0.015
  density : Float32 := 1.0
  absVelocityThreshold : Float32 := 1
  deriving Inhabited

namespace SplineDecay

/-- Friction × AOSP's "magic" physical coefficient:
`g · 39.37 in/m · (160·density) px/in · 0.84` (the 0.84 is AOSP's
"look and feel tuning"). ≈ 778.4 px/s² at density 1. -/
private def frictionCoeff (d : SplineDecay) : Float :=
  d.friction.toFloat * (9.80665 * 39.37 * (d.density.toFloat * 160.0) * 0.84)

/-- The spline deceleration exponent `l = ln(inflection·|v₀| / (friction·magic))`. -/
private def splineDeceleration (d : SplineDecay) (v0 : Float32) : Float :=
  (inflection * v0.toFloat.abs / d.frictionCoeff).log

/-- Total fling duration: `exp(l / (rate − 1))` seconds, in ns. -/
def durationNs (d : SplineDecay) (v0 : Float32) : UInt64 :=
  if v0.abs ≤ d.absVelocityThreshold then 0
  else (1e9 * (d.splineDeceleration v0 / (decelerationRate - 1.0)).exp).toUInt64

/-- Total fling travel (unsigned px):
`friction·magic · exp(rate/(rate−1) · l)`. -/
def distance (d : SplineDecay) (v0 : Float32) : Float32 :=
  if v0.abs ≤ d.absVelocityThreshold then 0
  else
    (d.frictionCoeff *
      (decelerationRate / (decelerationRate - 1.0) * d.splineDeceleration v0).exp).toFloat32

/-- Where the fling stops: `x₀ ± distance` along the velocity's sign. -/
def targetValue (d : SplineDecay) (x0 v0 : Float32) : Float32 :=
  if v0 < 0 then x0 - d.distance v0 else x0 + d.distance v0

/-- Position at `tNs`, starting from `x0` at `v0` px/s. -/
def valueAt (d : SplineDecay) (x0 v0 : Float32) (tNs : UInt64) : Float32 :=
  let dur := d.durationNs v0
  if dur == 0 then x0
  else
    let sign : Float := if v0 < 0 then -1.0 else 1.0
    let (distCoef, _) := flingPosition (tNs.toFloat / dur.toFloat)
    (x0.toFloat + sign * (d.distance v0).toFloat * distCoef).toFloat32

/-- Velocity at `tNs` after starting at `v0` px/s:
the spline slope × mean speed `distance/duration`. -/
def velocityAt (d : SplineDecay) (v0 : Float32) (tNs : UInt64) : Float32 :=
  let dur := d.durationNs v0
  if dur == 0 then 0
  else
    let sign : Float := if v0 < 0 then -1.0 else 1.0
    let (_, velCoef) := flingPosition (tNs.toFloat / dur.toFloat)
    (sign * (d.distance v0).toFloat / (dur.toFloat * 1e-9) * velCoef).toFloat32

/-- The decay for a display: real density in, AOSP friction default. -/
def ofDensity (den : Density) (friction : Float32 := 0.015) : SplineDecay :=
  { friction, density := den.density }

-- The fixture: v₀ = 1000 px/s at density 1 (hand-derived from the exact
-- formulas: l = ln(350/778.35) ≈ −0.7992, duration = e^(l/1.3582) ≈ 0.5552 s,
-- distance = 778.35·e^(2.3582/1.3582·l) ≈ 194.3 px).
#guard ((({} : SplineDecay).durationNs 1000).toFloat / 1e9 - 0.5552).abs < 0.006
#guard (({} : SplineDecay).distance 1000 - 194.3).abs < 2
-- The INFLEXION identity: distance = 0.35 · v₀ · duration.
#guard (({} : SplineDecay).distance 1000
        - 0.35 * 1000 * ((({} : SplineDecay).durationNs 1000).toFloat32 / 1e9)).abs < 2
-- Launch velocity reads back off the table within its resolution.
#guard (({} : SplineDecay).velocityAt 1000 0 - 1000).abs < 30
#guard (({} : SplineDecay).valueAt 0 1000 0).abs < 0.1
-- By the end the full distance is covered and the velocity is spent.
#guard (({} : SplineDecay).valueAt 0 1000 (({} : SplineDecay).durationNs 1000)
        - ({} : SplineDecay).distance 1000).abs < 0.01
#guard ({} : SplineDecay).velocityAt 1000 (({} : SplineDecay).durationNs 1000) == 0
-- Negative velocity mirrors.
#guard (({} : SplineDecay).targetValue 500 (-1000) - (500 - 194.3)).abs < 2
-- Faster flings coast disproportionately farther (spline superlinearity).
#guard ({} : SplineDecay).distance 4000 > 4 * ({} : SplineDecay).distance 1000
-- Higher density (more px per inch) covers more px for the same px/s.
#guard ({ density := 3 : SplineDecay }).distance 1000 < ({} : SplineDecay).distance 1000
-- Sub-threshold velocity: nothing to animate.
#guard ({} : SplineDecay).durationNs 0.5 == 0

end SplineDecay

end Compose

end
