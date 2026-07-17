module

public section

namespace Compose

/-!
# Overscroll physics (`Compose/Foundation/Overscroll.lean`)

Two overscroll models, both pure and `#guard`-tested here; the
integration (drag, release, fling-into-edge) lives in
`Compose/Foundation/Scroll.lean`, and `OverscrollMode` picks between
them per scrollable:

- **Stretch** (`.stretch`, the default): Android 12+'s `EdgeEffect` —
  the raw pull distance maps through a damped intensity curve (capped
  at ~3.2% of the viewport) and renders as a GPU content warp
  (`LayerEffect.stretch`); release runs AOSP's near-critical spring
  with a linear-glide endgame. Constants and formulas are ported from
  `frameworks/base/core/java/android/widget/EdgeEffect.java`.
- **Bounce** (`.bounce`): the translation-based rubber band from
  Compose Multiplatform's `CupertinoOverscrollEffect` (Apple's curve
  and spring constants) — the model Compose ships where the stretch
  doesn't exist.
-/

/-- Which overscroll visual a scrollable uses at its range ends.
`stretch` is the Android 12+ `EdgeEffect` content warp (the default),
`bounce` the Cupertino translation rubber band, `none` a hard stop. -/
inductive OverscrollMode where
  | stretch
  | bounce
  | none
  deriving Repr, BEq, Inhabited

/-- Modifier-key discriminant: mode switches must invalidate the scroll
modifier's identity-keyed elements. -/
def OverscrollMode.key : OverscrollMode → UInt64
  | .stretch => 0
  | .bounce => 1
  | .none => 2

#guard OverscrollMode.stretch.key != OverscrollMode.bounce.key
        && OverscrollMode.bounce.key != OverscrollMode.none.key

/-- Apple/CMP rubber-band coefficient (`RUBBER_BAND_COEFFICIENT`). -/
def rubberBandCoefficient : Float32 := 0.55

/-- The visible overscroll for raw over-range drag distance `x` against
viewport dimension `d`: `sign(x)·(1 − 1/(|x|·c/d + 1))·d` — linear near
the edge, asymptotically capped at `d`. Mirrors CMP
`CupertinoOverscrollEffect`'s rubber-banding. -/
def rubberBand (x d : Float32) (c : Float32 := rubberBandCoefficient) : Float32 :=
  if d ≤ 0 then 0
  else
    let sign : Float32 := if x < 0 then -1 else 1
    sign * (1 - 1 / (x.abs * c / d + 1)) * d

/-- Inverse of `rubberBand`: the raw drag distance whose rubber-banded
image is `vis` — `(d/c)·|vis|/(d − |vis|)`, signed. `|vis|` is clamped
just under `d` (the asymptote is unreachable from `rubberBand`). -/
def rubberBandInverse (vis d : Float32) (c : Float32 := rubberBandCoefficient) : Float32 :=
  if d ≤ 0 then 0
  else
    let sign : Float32 := if vis < 0 then -1 else 1
    let a := min vis.abs (d - 0.001)
    sign * (d / c) * a / (d - a)

-- No pull, no band; a degenerate viewport stays inert.
#guard rubberBand 0 100 == 0
#guard rubberBand 50 0 == 0 && rubberBandInverse 50 0 == 0
-- The hand value: a full-viewport pull shows (1 − 1/1.55)·100 ≈ 35.48 px.
#guard (rubberBand 100 100 - 35.4839).abs < 0.001
-- Odd symmetry, monotonicity, and the asymptote below the viewport size.
#guard rubberBand (-100) 100 == -(rubberBand 100 100)
#guard rubberBand 50 100 < rubberBand 100 100
        && rubberBand 100 100 < rubberBand 200 100
#guard rubberBand 100000 100 < 100
-- The inverse round-trips the forward map (both signs).
#guard (rubberBandInverse (rubberBand 80 100) 100 - 80).abs < 0.01
#guard (rubberBandInverse (rubberBand (-30) 100) 100 + 30).abs < 0.01
#guard (rubberBand (rubberBandInverse 20 100) 100 - 20).abs < 0.01

/-- Spring-back stiffness (CMP: `Spring.StiffnessLow`). -/
def overscrollStiffness : Float32 := 200

/-- Spring-back damping: critically damped — the visible "bounce" is the
overshoot a fling's residual velocity buys, not oscillation. -/
def overscrollDamping : Float32 := 1.0

/-- Spring-back settle threshold, px (CMP's 0.5). -/
def overscrollVisibilityThreshold : Float32 := 0.5

/-!
## Stretch (`EdgeEffect`) twins

All constants are AOSP `EdgeEffect.java` verbatim: the two 0.016
intensity gains (`LINEAR_STRETCH_INTENSITY`/`EXP_STRETCH_INTENSITY`),
the 0.33 exponential range (`SCROLL_DIST_AFFECTED_BY_EXP_STRETCH`), the
ω₀ = 24.657 rad/s / ζ = 0.98 return spring (`NATURAL_FREQUENCY`/
`DAMPING_RATIO`), the ×13 fling absorb (`ON_ABSORB_VELOCITY_ADJUSTMENT`),
and the 200 px/s / 8 px linear-glide endgame with its 0.001 px /
0.01 px/s settle thresholds.
-/

/-- Linear gain of the pull→intensity curve (`LINEAR_STRETCH_INTENSITY`). -/
def stretchLinearIntensity : Float32 := 0.016

/-- Exponential gain of the pull→intensity curve (`EXP_STRETCH_INTENSITY`). -/
def stretchExpIntensity : Float32 := 0.016

/-- Fraction of the viewport over which the exponential term saturates
(`SCROLL_DIST_AFFECTED_BY_EXP_STRETCH`). -/
def stretchExpRange : Float32 := 0.33

/-- How strongly the warp eases off away from the pinned edge — the
shader's `uInterpolationStrength` (`StretchEffect.cpp`). Cited by
`Gpu.Sdf.stretchPosUp`'s 0.7 literal. -/
def stretchInterpolationStrength : Float32 := 0.7

/-- Return-spring undamped frequency ω₀, rad/s (`NATURAL_FREQUENCY`). -/
def stretchNaturalFrequency : Float32 := 24.657

/-- Return-spring damping ratio ζ — just under critical, one tiny
overshoot (`DAMPING_RATIO`). -/
def stretchDampingRatio : Float32 := 0.98

/-- Endgame glide speed, px/s (`LINEAR_VELOCITY_TAKE_OVER`). -/
def stretchLinearVelocityTakeOver : Float32 := 200

/-- Endgame glide distance window, px (`LINEAR_DISTANCE_TAKE_OVER`). -/
def stretchLinearDistanceTakeOver : Float32 := 8

/-- Settled when the magnitude is below this, px (`VALUE_THRESHOLD`). -/
def stretchValueThreshold : Float32 := 0.001

/-- …and the speed is below this, px/s (`VELOCITY_THRESHOLD`). -/
def stretchVelocityThreshold : Float32 := 0.01

/-- Fling-into-edge velocity boost (`ON_ABSORB_VELOCITY_ADJUSTMENT`). -/
def stretchAbsorbFactor : Float32 := 13

/-- Signed stretch intensity for raw pull distance `pull` px against
viewport dimension `viewport` px (`EdgeEffect.dampStretchVector`):
with `d = clamp(|pull|/viewport, 0, 1)`,
`sign · (0.016·d + 0.016·(1 − e^(−d·e/0.33)))` — linear near the edge,
the exponential term saturating over the first third of the viewport.
Maximum ≈ 0.032: content never stretches more than ~3.2%. Zero for a
degenerate viewport. -/
def stretchIntensity (pull viewport : Float32) : Float32 :=
  if viewport ≤ 0 then 0
  else
    let sign : Float32 := if pull < 0 then -1 else 1
    let d := (min (pull.abs / viewport) 1).toFloat
    let scalar := Float.exp 1 / stretchExpRange.toFloat
    let expPart := 1 - Float.exp (-(d * scalar))
    sign * (stretchLinearIntensity * d.toFloat32
            + stretchExpIntensity * expPart.toFloat32)

-- No pull, no stretch; a degenerate viewport stays inert.
#guard stretchIntensity 0 100 == 0
#guard stretchIntensity 50 0 == 0
-- Odd symmetry, monotonicity, and the full-viewport clamp.
#guard stretchIntensity (-50) 100 == -(stretchIntensity 50 100)
#guard stretchIntensity 10 100 < stretchIntensity 50 100
        && stretchIntensity 50 100 < stretchIntensity 100 100
#guard stretchIntensity 500 100 == stretchIntensity 100 100
-- Hand pins (scalar e/0.33 = 8.237218): d = 1 → 0.016·(1 + (1 − e^−8.2372))
-- ≈ 0.031996; d = 0.5 → ≈ 0.023740; d = 0.1 → ≈ 0.010579.
#guard (stretchIntensity 100 100 - 0.031996).abs < 1e-4
#guard (stretchIntensity 50 100 - 0.023740).abs < 1e-4
#guard (stretchIntensity 10 100 - 0.010579).abs < 1e-4

/-- One closed-form step of the underdamped return spring toward 0
(`EdgeEffect.updateSpring`): with ζω₀ decay and ωd = ω₀√(1−ζ²),
`x' = e^(−ζω₀Δt)·(x·cos(ωdΔt) + ((ζω₀x + v)/ωd)·sin(ωdΔt))` and
`v' = x'·(−ω₀ζ) + e^(−ζω₀Δt)·(−ωd·x·sin(ωdΔt) + (ζω₀x + v)·cos(ωdΔt))`
— AOSP's shipped form (its `v'` folds the decayed `x'` into the first
term rather than the textbook product rule; kept verbatim). -/
def stretchSpringStep (x v deltaT : Float32) : Float32 × Float32 :=
  let zw := (stretchDampingRatio * stretchNaturalFrequency).toFloat
  let wd := stretchNaturalFrequency.toFloat
            * Float.sqrt (1 - (stretchDampingRatio * stretchDampingRatio).toFloat)
  let xf := x.toFloat
  let dt := deltaT.toFloat
  let decay := Float.exp (-(zw * dt))
  let cosT := Float.cos (wd * dt)
  let sinT := Float.sin (wd * dt)
  let pushed := zw * xf + v.toFloat
  let x' := decay * (xf * cosT + pushed / wd * sinT)
  let v' := x' * (-zw) + decay * (-(wd * xf * sinT) + pushed * cosT)
  (x'.toFloat32, v'.toFloat32)

-- The spring decays; hand pin at Δt = 1/60 from (100, 0): ζω₀ = 24.16386,
-- ωd = 4.90668, e^(−0.402731) = 0.668491 → x' ≈ 93.52 (and v' pulls home).
#guard (stretchSpringStep 100 0 (1/60)).1 < 100
#guard ((stretchSpringStep 100 0 (1/60)).1 - 93.52).abs < 0.05
#guard (stretchSpringStep 100 0 (1/60)).2 < 0
-- 120 steps (two seconds) from a 100 px band land at rest.
#guard Id.run do
  let mut s : Float32 × Float32 := (100, 0)
  for _ in [0:120] do
    s := stretchSpringStep s.1 s.2 (1/60)
  return s.1.abs < 0.5

/-- One frame of the full `EdgeEffect` settle on a non-negative band
magnitude `x` px (the driver factors the sign out): the constant-speed
linear glide takes over near home (|v| ≤ 200 px/s, x < 8 px, v headed
home) to skip the near-critical spring's asymptotic crawl — arriving on
its zero-crossing; otherwise one `stretchSpringStep`, clamped to the
viewport (velocity zeroed on clamp), settled below the value+velocity
thresholds or on overshoot past 0. Returns `(x', v', settled)`. -/
def stretchSettleStep (x v deltaT viewport : Float32) :
    Float32 × Float32 × Bool :=
  if v < 0 && v.abs ≤ stretchLinearVelocityTakeOver
      && x < stretchLinearDistanceTakeOver then
    let x' := x - stretchLinearVelocityTakeOver * deltaT
    if x' ≤ 0 then (0, 0, true)
    else (x', -stretchLinearVelocityTakeOver, false)
  else
    let (x', v') := stretchSpringStep x v deltaT
    if x' < 0 then (0, 0, true)
    else if x' < stretchValueThreshold && v'.abs < stretchVelocityThreshold then
      (0, 0, true)
    else if x' > viewport then (viewport, 0, false)
    else (x', v', false)

-- Glide branch: 4 px at −100 px/s glides 200·0.016 = 3.2 px…
#guard (stretchSettleStep 4 (-100) 0.016 100).1 == 4 - 200 * (0.016 : Float32)
#guard (stretchSettleStep 4 (-100) 0.016 100).2.1 == -200
#guard (stretchSettleStep 4 (-100) 0.016 100).2.2 == false
-- …and arrives exactly on the zero-crossing.
#guard stretchSettleStep 0.5 (-200) 0.016 100 == (0, 0, true)
-- Spring branch: a 50 px band at rest starts home, unsettled…
#guard (stretchSettleStep 50 0 (1/60) 100).1 < 50
        && (stretchSettleStep 50 0 (1/60) 100).1 > 0
#guard (stretchSettleStep 50 0 (1/60) 100).2.2 == false
-- …an outward fling clamps at the viewport with velocity zeroed…
#guard stretchSettleStep 120 5000 0.016 100 == (100, 0, false)
-- …and a sub-threshold band settles.
#guard (stretchSettleStep 0.0005 0.005 0.016 100).2.2 == true

end Compose

end
