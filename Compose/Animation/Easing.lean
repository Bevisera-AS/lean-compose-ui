module

public section

namespace Compose

/-!
# Easing (`Compose/Animation/Easing.lean`)

Time-fraction interpolators for tween/keyframe animations, mirroring
`androidx.compose.animation.core.Easing`. `cubicBezier` solves the curve's
`x(t) = fraction` numerically (bisection on the monotone x-polynomial, like
Compose's `CubicBezierEasing`), accurate to well under `1e-4`.
-/

/-- Maps a fraction of elapsed animation time in `[0, 1]` to a fraction of
progress (0 = start value, 1 = end value; values outside `[0, 1]` mean
over/undershoot). Mirrors `androidx.compose.animation.core.Easing`. -/
structure Easing where
  /-- The interpolation function. Mirrors `Easing.transform`. -/
  transform : Float32 → Float32

instance : Inhabited Easing := ⟨⟨fun f => f⟩⟩

namespace Easing

/-- One coordinate of a cubic Bézier with endpoints `0`/`1` and inner control
values `p1`, `p2`, at parameter `t`. -/
private def bezierCoord (p1 p2 t : Float32) : Float32 :=
  let u := 1.0 - t
  3.0 * p1 * t * u * u + 3.0 * p2 * t * t * u + t * t * t

/-- The identity easing. Mirrors
`androidx.compose.animation.core.LinearEasing`. -/
def linear : Easing := ⟨fun f => f⟩

/-- Third-order Bézier easing through `(0,0)`, `(a,b)`, `(c,d)`, `(1,1)`:
solve `x(t) = fraction` by bisection (32 halvings — `x` is monotone for
control x-values in `[0, 1]`), then return `y(t)`. Mirrors
`androidx.compose.animation.core.CubicBezierEasing`. -/
def cubicBezier (a b c d : Float32) : Easing := ⟨fun x =>
  if x <= 0.0 then 0.0
  else if x >= 1.0 then 1.0
  else Id.run do
    let mut lo : Float32 := 0.0
    let mut hi : Float32 := 1.0
    for _ in [0:32] do
      let mid := (lo + hi) / 2.0
      if bezierCoord a c mid < x then lo := mid else hi := mid
    return bezierCoord b d ((lo + hi) / 2.0)⟩

/-- The Material standard curve `(0.4, 0, 0.2, 1)`: starts fast, ends slow.
Mirrors `androidx.compose.animation.core.FastOutSlowInEasing`. -/
def fastOutSlowIn : Easing := cubicBezier 0.4 0.0 0.2 1.0

/-- The incoming-element curve `(0, 0, 0.2, 1)`. Mirrors
`androidx.compose.animation.core.LinearOutSlowInEasing`. -/
def linearOutSlowIn : Easing := cubicBezier 0.0 0.0 0.2 1.0

/-- The outgoing-element curve `(0.4, 0, 1, 1)`. Mirrors
`androidx.compose.animation.core.FastOutLinearInEasing`. -/
def fastOutLinearIn : Easing := cubicBezier 0.4 0.0 1.0 1.0

/-- `|x − y| ≤ tol`, the tolerance comparison used by the animation-math
guards. -/
def approx (x y : Float32) (tol : Float32 := 0.0001) : Bool :=
  (x - y).abs <= tol

-- endpoints are exact for every curve
#guard fastOutSlowIn.transform 0.0 == 0.0
#guard fastOutSlowIn.transform 1.0 == 1.0
#guard linearOutSlowIn.transform 0.0 == 0.0
#guard fastOutLinearIn.transform 1.0 == 1.0
#guard linear.transform 0.37 == 0.37
-- out-of-range inputs clamp
#guard fastOutSlowIn.transform (-0.5) == 0.0
#guard fastOutSlowIn.transform 1.5 == 1.0
-- known curve values (solved analytically to 4 decimals)
#guard approx (fastOutSlowIn.transform 0.5) 0.7756 (tol := 0.001)
#guard approx (linearOutSlowIn.transform 0.5) 0.8392 (tol := 0.001)
#guard approx (fastOutLinearIn.transform 0.5) 0.3249 (tol := 0.001)
-- a bézier with linear control points is the identity (checks the solver)
#guard approx ((cubicBezier (1.0/3.0) (1.0/3.0) (2.0/3.0) (2.0/3.0)).transform 0.25) 0.25
#guard approx ((cubicBezier (1.0/3.0) (1.0/3.0) (2.0/3.0) (2.0/3.0)).transform 0.8) 0.8
-- fastOutSlowIn is ahead of linear early-mid, monotone
#guard fastOutSlowIn.transform 0.25 < fastOutSlowIn.transform 0.5
#guard fastOutSlowIn.transform 0.5 < fastOutSlowIn.transform 0.75
#guard fastOutSlowIn.transform 0.5 > 0.5

end Easing

end Compose

end
