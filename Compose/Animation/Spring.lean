namespace Compose

/-!
# Spring physics (`Compose/Animation/Spring.lean`)

The closed-form solutions of the damped harmonic oscillator
`x'' + 2ζω x' + ω² x = 0` (mass 1, natural frequency `ω = √stiffness`,
displacement measured from the target), split into the under-, critically-,
and over-damped cases — a direct port of
`androidx.compose.animation.core.SpringSimulation.updateValues`. Evaluation
is done in 64-bit floats (the exponentials are precision-sensitive) and
truncated to `Float32` at the boundary.

An animation is considered settled when **both** the displacement and the
velocity are under threshold (`isAtEquilibrium`), with Compose's velocity
threshold of `62.5 × valueThreshold` per second (`1000/16`).
-/

namespace Spring

/-- No bounce (critical damping). Mirrors `Spring.DampingRatioNoBouncy`. -/
def dampingRatioNoBouncy : Float32 := 1.0
/-- Low bounciness. Mirrors `Spring.DampingRatioLowBouncy`. -/
def dampingRatioLowBouncy : Float32 := 0.75
/-- Medium bounciness. Mirrors `Spring.DampingRatioMediumBouncy`. -/
def dampingRatioMediumBouncy : Float32 := 0.5
/-- High bounciness. Mirrors `Spring.DampingRatioHighBouncy`. -/
def dampingRatioHighBouncy : Float32 := 0.2

/-- Very stiff. Mirrors `Spring.StiffnessHigh`. -/
def stiffnessHigh : Float32 := 10000.0
/-- Default stiffness. Mirrors `Spring.StiffnessMedium`. -/
def stiffnessMedium : Float32 := 1500.0
/-- Medium-low stiffness. Mirrors `Spring.StiffnessMediumLow`. -/
def stiffnessMediumLow : Float32 := 400.0
/-- Low stiffness. Mirrors `Spring.StiffnessLow`. -/
def stiffnessLow : Float32 := 200.0
/-- Very low stiffness. Mirrors `Spring.StiffnessVeryLow`. -/
def stiffnessVeryLow : Float32 := 50.0

/-- Default value-settling threshold when a spec provides no
`visibilityThreshold`. Mirrors `SpringSpec`'s default of `0.01`. -/
def defaultDisplacementThreshold : Float32 := 0.01

/-- Velocity threshold per unit of value threshold, in units/second. Mirrors
`SpringSimulation`'s `VelocityThresholdMultiplier` (`1000 / 16`). -/
def velocityThresholdMultiplier : Float32 := 62.5

/-- `(value, velocity)` of the damped spring at `tSec` seconds, given the
start value, the target (rest) value, the start velocity `v0`
(units/second), the damping ratio `ζ`, and the stiffness `k` (mass 1).
Mirrors `SpringSimulation.updateValues`. -/
def evaluate (dampingRatio stiffness : Float32) (start target v0 : Float32)
    (tSec : Float32) : Float32 × Float32 :=
  let ζ := dampingRatio.toFloat
  let ω := stiffness.toFloat.sqrt
  let x0 := (start - target).toFloat
  let v0 := v0.toFloat
  let t := tSec.toFloat
  let (disp, vel) :=
    if ζ > 1.0 then
      -- Overdamped: x = c₁·e^{γ₋t} + c₂·e^{γ₊t} with both roots negative.
      let s := (ζ * ζ - 1.0).sqrt
      let γplus := (-ζ + s) * ω
      let γminus := (-ζ - s) * ω
      let c2 := (γminus * x0 - v0) / (γminus - γplus)
      let c1 := x0 - c2
      let eMinus := (γminus * t).exp
      let ePlus := (γplus * t).exp
      (c1 * eMinus + c2 * ePlus, c1 * γminus * eMinus + c2 * γplus * ePlus)
    else if ζ == 1.0 then
      -- Critically damped: x = (c₁ + c₂t)·e^{−ωt}.
      let c1 := x0
      let c2 := v0 + ω * x0
      let e := (-ω * t).exp
      ((c1 + c2 * t) * e, (c2 - ω * (c1 + c2 * t)) * e)
    else
      -- Underdamped: x = e^{−ζωt}·(c₁cos(ω_d t) + c₂sin(ω_d t)).
      let ωd := ω * (1.0 - ζ * ζ).sqrt
      let c1 := x0
      let c2 := (ζ * ω * x0 + v0) / ωd
      let e := (-ζ * ω * t).exp
      let cosT := (ωd * t).cos
      let sinT := (ωd * t).sin
      let x := e * (c1 * cosT + c2 * sinT)
      (x, -ζ * ω * x + e * ωd * (c2 * cosT - c1 * sinT))
  ((target.toFloat + disp).toFloat32, vel.toFloat32)

/-- Whether the spring has settled: displacement under `valueThreshold` and
velocity under `valueThreshold × 62.5`/s. Mirrors
`SpringSimulation.isAtEquilibrium` with Compose's threshold coupling. -/
def isAtEquilibrium (target valueThreshold value velocity : Float32) : Bool :=
  (value - target).abs < valueThreshold &&
    velocity.abs < valueThreshold * velocityThresholdMultiplier

/-! Guards evaluate a unit step (`0 → 1`) at various damping ratios. -/

private def approx (x y : Float32) (tol : Float32 := 0.0001) : Bool :=
  (x - y).abs <= tol

private def valAt (ζ k t : Float32) (v0 : Float32 := 0) : Float32 :=
  (evaluate ζ k 0.0 1.0 v0 t).1
private def velAt (ζ k t : Float32) (v0 : Float32 := 0) : Float32 :=
  (evaluate ζ k 0.0 1.0 v0 t).2

-- t = 0 reproduces the initial conditions exactly, in every regime
#guard (evaluate 1.0 1500 3 8 (-2) 0) == (3, -2)
#guard (evaluate 0.5 400 3 8 (-2) 0) == (3, -2)
#guard approx (valAt 2.0 400 0 (v0 := 5)) 0 && approx (velAt 2.0 400 0 (v0 := 5)) 5
-- long-time limit is the target with ~zero velocity
#guard approx (valAt 1.0 1500 10) 1 && approx (velAt 1.0 1500 10) 0
#guard approx (valAt 0.2 100 10) 1
#guard approx (valAt 3.0 100 10) 1
-- critical damping approaches monotonically (never overshoots)
#guard valAt 1.0 100 0.05 < valAt 1.0 100 0.1
#guard valAt 1.0 100 0.1 < valAt 1.0 100 0.3
#guard valAt 1.0 100 0.3 < valAt 1.0 100 1.0
#guard valAt 1.0 100 5.0 <= 1.0
-- underdamped overshoots at t = π/ω_d (peak = 1 + e^{−ζωπ/ω_d}), then converges
#guard valAt 0.2 100 0.3206 > 1.3
#guard approx (valAt 0.2 100 0.3206) 1.5266 (tol := 0.001)
#guard approx (velAt 0.2 100 0.3206) 0 (tol := 0.01)   -- velocity ≈ 0 at the peak
#guard approx (valAt 0.2 100 6.0) 1 (tol := 0.001)
-- overdamped is slower than critical but also monotone
#guard valAt 3.0 100 0.3 < valAt 1.0 100 0.3
#guard valAt 3.0 100 0.3 < valAt 3.0 100 0.6
-- a positive start velocity moves the value further along initially
#guard valAt 1.0 100 0.05 (v0 := 10) > valAt 1.0 100 0.05
-- equilibrium test couples value and velocity thresholds
#guard isAtEquilibrium 1.0 0.01 1.005 0.1
#guard !isAtEquilibrium 1.0 0.01 1.02 0.1
#guard !isAtEquilibrium 1.0 0.01 1.005 10.0

end Spring

end Compose
