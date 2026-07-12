import Compose.Core.Geometry

/-!
# GPU SDF math, pure twins (`Compose/Ui/Draw/Gpu/Sdf.lean`)

The signed-distance-field, coverage, and Gaussian-shadow math the GPU quad and
shadow fragment shaders evaluate (`Gpu/Shaders.lean`), duplicated as pure Lean
functions so the formulas are compile-time-tested by `#guard`s even though MSL
source is not. Every function here must stay in lockstep with its MSL twin —
the shader strings cite these names.

The shadow math is Evan Wallace's analytic rounded-rectangle Gaussian
(closed-form `erf` integral along x, 4-sample midpoint quadrature along y over
`±3σ`; madebyevan.com/shaders/fast-rounded-rectangle-shadows). Wired into the
shadow pipeline in milestone M-c; the math lives here from M-b.
-/

namespace Compose.Draw.Gpu

/-- `saturate` (clamp to `[0, 1]`), as in MSL. -/
def saturate (x : Float32) : Float32 := min 1 (max 0 x)

/-- The corner radius governing point `p` of a rounded rect centered at
`center`: the quadrant containing `p` picks from `(tl, tr, br, bl)`. -/
def pickRadius (p center : Offset) (tl tr br bl : Float32) : Float32 :=
  if p.x < center.x then (if p.y < center.y then tl else bl)
  else (if p.y < center.y then tr else br)

/-- Signed distance from `p` to a rounded rect given as origin `o`, size
`half * 2`, and per-corner radii — negative inside, zero on the boundary,
positive outside (the standard 2D rounded-box SDF). -/
def rrectSdf (p o : Offset) (size : Size) (tl tr br bl : Float32) : Float32 :=
  let hw := size.width / 2
  let hh := size.height / 2
  let center : Offset := ⟨o.x + hw, o.y + hh⟩
  let r := pickRadius p center tl tr br bl
  let dx := (p.x - center.x).abs - hw + r
  let dy := (p.y - center.y).abs - hh + r
  let ox := max dx 0
  let oy := max dy 0
  (ox * ox + oy * oy).sqrt + min (max dx dy) 0 - r

/-- Analytic antialiased coverage of an SDF evaluated at a pixel center:
full one pixel inside, zero one pixel outside, linear across the boundary. -/
def coverage (sdf : Float32) : Float32 := saturate (0.5 - sdf)

-- Rect SDF (radius 0): inside is negative, boundary zero, outside positive.
#guard rrectSdf ⟨5, 5⟩ ⟨0, 0⟩ ⟨10, 10⟩ 0 0 0 0 == -5
#guard rrectSdf ⟨0, 5⟩ ⟨0, 0⟩ ⟨10, 10⟩ 0 0 0 0 == 0
#guard rrectSdf ⟨-3, 5⟩ ⟨0, 0⟩ ⟨10, 10⟩ 0 0 0 0 == 3
-- A circle as an all-corner-radius rounded square: distance from center is
-- `|p - c| - r`.
#guard rrectSdf ⟨10, 10⟩ ⟨0, 0⟩ ⟨20, 20⟩ 10 10 10 10 == -10
#guard rrectSdf ⟨20, 10⟩ ⟨0, 0⟩ ⟨20, 20⟩ 10 10 10 10 == 0
#guard rrectSdf ⟨25, 10⟩ ⟨0, 0⟩ ⟨20, 20⟩ 10 10 10 10 == 5
-- Corner-quadrant selection: only the top-left corner is rounded, so the
-- top-left diagonal is outside at the corner point while bottom-right is not.
#guard rrectSdf ⟨0, 0⟩ ⟨0, 0⟩ ⟨20, 20⟩ 8 0 0 0 > 0
#guard rrectSdf ⟨20, 20⟩ ⟨0, 0⟩ ⟨20, 20⟩ 8 0 0 0 == 0
-- Coverage: deep inside 1, far outside 0, boundary ½.
#guard coverage (-5) == 1
#guard coverage 5 == 0
#guard coverage 0 == 0.5

/-! ## Analytic Gaussian shadow (Evan Wallace) -/

/-- The Gaussian PDF with standard deviation `sigma`. -/
def gaussian (x sigma : Float32) : Float32 :=
  let twoPi : Float32 := 6.28318530717958647692
  ((-(x * x) / (2 * sigma * sigma)).toFloat.exp).toFloat32 / (twoPi.sqrt * sigma)

/-- 4-term Abramowitz & Stegun `erf` approximation (7.1.25, |ε| ≤ 5·10⁻⁴) —
the cheap error function the shadow shader evaluates. -/
def erf4 (x : Float32) : Float32 :=
  let s : Float32 := if x < 0 then -1 else 1
  let a := x.abs
  let t := 1 + (0.278393 + (0.230389 + 0.078108 * (a * a)) * a) * a
  let t2 := t * t
  s - s / (t2 * t2)

/-- Closed-form x-integral of the Gaussian-blurred rounded rectangle at row
offset `y` (Wallace's `roundedBoxShadowX`): the rounded corner shrinks the
covered x-interval as `y` approaches the corner band. `halfW`/`halfH` are the
rect half-extents, `corner` its (circular) corner radius. -/
def shadowX (x y sigma corner halfW halfH : Float32) : Float32 :=
  let delta := min (halfH - corner - y.abs) 0
  let curved := halfW - corner + (max (corner * corner - delta * delta) 0).sqrt
  let sqrtHalf : Float32 := 0.70710678118654752440
  let lo := 0.5 + 0.5 * erf4 ((x - curved) * (sqrtHalf / sigma))
  let hi := 0.5 + 0.5 * erf4 ((x + curved) * (sqrtHalf / sigma))
  hi - lo

/-- Gaussian-blurred coverage of a rounded rectangle at `p` (rect from `o` of
`size`, circular `corner` radius, blur `sigma`): closed form along x,
4-sample midpoint quadrature along y clamped to `±3σ` (Wallace's
`roundedBoxShadow`). -/
def shadow (p o : Offset) (size : Size) (corner sigma : Float32) : Float32 := Id.run do
  let halfW := size.width / 2
  let halfH := size.height / 2
  let c : Offset := ⟨o.x + halfW, o.y + halfH⟩
  let pt := p - c
  let low := pt.y - halfH
  let high := pt.y + halfH
  let start := min (max (-3 * sigma) low) high
  let stop := min (max (3 * sigma) low) high
  let step := (stop - start) / 4
  let mut y := start + step * 0.5
  let mut value : Float32 := 0
  for _ in [0:4] do
    value := value + shadowX pt.x (pt.y - y) sigma corner halfW halfH * gaussian y sigma * step
    y := y + step
  return value

-- erf: odd, saturating, zero at zero.
#guard erf4 0 == 0
#guard (erf4 3 - 1).abs < 0.001
#guard (erf4 (-3) + 1).abs < 0.001
#guard (erf4 0.5 + erf4 (-0.5)).abs < 1e-6
-- Gaussian: symmetric, peak at 0.
#guard (gaussian 1 2 - gaussian (-1) 2).abs < 1e-6
#guard gaussian 0 2 > gaussian 1 2
-- Shadow of a large rect at its center ≈ 1; far away ≈ 0; boundary ≈ ½.
#guard (shadow ⟨50, 50⟩ ⟨0, 0⟩ ⟨100, 100⟩ 0 4 - 1).abs < 0.01
#guard (shadow ⟨200, 50⟩ ⟨0, 0⟩ ⟨100, 100⟩ 0 4).abs < 0.01
#guard (shadow ⟨100, 50⟩ ⟨0, 0⟩ ⟨100, 100⟩ 0 4 - 0.5).abs < 0.02
-- Symmetry across the rect center.
#guard (shadow ⟨30, 20⟩ ⟨0, 0⟩ ⟨100, 100⟩ 8 5 - shadow ⟨70, 80⟩ ⟨0, 0⟩ ⟨100, 100⟩ 8 5).abs < 1e-4
-- Rounding a corner removes shadow mass near that corner.
#guard shadow ⟨2, 2⟩ ⟨0, 0⟩ ⟨40, 40⟩ 12 3 < shadow ⟨2, 2⟩ ⟨0, 0⟩ ⟨40, 40⟩ 0 3

end Compose.Draw.Gpu
