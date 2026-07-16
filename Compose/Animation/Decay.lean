module

public section

namespace Compose

/-!
# Decay animation (`Compose/Animation/Decay.lean`)

The target-less half of the animation story: a fling has an initial velocity
and *decays* — where it stops falls out of the physics, unlike a tween's
fixed target. `ExponentialDecay` mirrors
`androidx.compose.animation.core.exponentialDecay`
(`FloatExponentialDecaySpec`): velocity decays as `v₀·e^(−f·t)`, so the
position approaches `x₀ + v₀/f` along `x₀ + v₀/f·(1 − e^(−f·t))`.

Consumed by `ScrollState.fling` (`Compose/Foundation/Scroll.lean`); the
evaluation is pure and `#guard`-tested here.
-/

/-- Exponential fling decay. `friction` is per-second (higher stops sooner;
Compose's default multiplier ×4.2); the fling ends when the speed falls
under `absVelocityThreshold` (px/s). -/
structure ExponentialDecay where
  friction : Float32 := 4.2
  absVelocityThreshold : Float32 := 1
  deriving Inhabited

namespace ExponentialDecay

/-- `friction` guarded positive (a zero/negative friction never settles). -/
private def f (d : ExponentialDecay) : Float := max d.friction.toFloat 1e-3

/-- Velocity at `tNs` after starting at `v0` px/s. -/
def velocityAt (d : ExponentialDecay) (v0 : Float32) (tNs : UInt64) : Float32 :=
  (v0.toFloat * (-d.f * tNs.toFloat * 1e-9).exp).toFloat32

/-- Position at `tNs`, starting from `x0` at `v0` px/s. -/
def valueAt (d : ExponentialDecay) (x0 v0 : Float32) (tNs : UInt64) : Float32 :=
  (x0.toFloat + v0.toFloat / d.f * (1.0 - (-d.f * tNs.toFloat * 1e-9).exp)).toFloat32

/-- Where the fling converges: `x₀ + v₀/friction`. -/
def targetValue (d : ExponentialDecay) (x0 v0 : Float32) : Float32 :=
  (x0.toFloat + v0.toFloat / d.f).toFloat32

/-- Time until the speed decays under `absVelocityThreshold`
(`ln(|v₀|/threshold)/friction`); `0` when already under it. -/
def durationNs (d : ExponentialDecay) (v0 : Float32) : UInt64 :=
  let thr := max d.absVelocityThreshold.toFloat 1e-3
  let v := v0.toFloat.abs
  if v ≤ thr then 0
  else ((v / thr).log / d.f * 1e9).toUInt64

-- The fixture: friction 2/s, v₀ 1000 px/s from x₀ = 0.
-- Convergence point is exactly v₀/friction.
#guard ({ friction := 2 : ExponentialDecay }).targetValue 0 1000 == 500
-- At t = 0 nothing has decayed and nothing has moved.
#guard ({ friction := 2 : ExponentialDecay }).velocityAt 1000 0 == 1000
#guard ({ friction := 2 : ExponentialDecay }).valueAt 0 1000 0 == 0
-- At t = 0.5 s: v = 1000·e⁻¹ ≈ 367.88, x = 500·(1 − e⁻¹) ≈ 316.06.
#guard (({ friction := 2 : ExponentialDecay }).velocityAt 1000 500_000_000
        - 367.8794).abs < 0.01
#guard (({ friction := 2 : ExponentialDecay }).valueAt 0 1000 500_000_000
        - 316.0603).abs < 0.01
-- Negative velocity mirrors: the fling runs toward the start.
#guard ({ friction := 2 : ExponentialDecay }).targetValue 500 (-1000) == 0
-- Duration: 1000 → 1 px/s at friction 2 is ln(1000)/2 ≈ 3.454 s.
#guard (({ friction := 2 : ExponentialDecay }).durationNs 1000).toFloat / 1e9
        - 3.4538 < 0.001
-- Sub-threshold velocity: nothing to animate.
#guard ({ friction := 2 : ExponentialDecay }).durationNs 0.5 == 0
-- By the computed end the velocity is (just) under the threshold.
#guard (({ friction := 2 : ExponentialDecay }).velocityAt 1000
          (({ friction := 2 : ExponentialDecay }).durationNs 1000)).abs ≤ 1.001

end ExponentialDecay

end Compose

end
