module

public section

namespace Compose

/-!
# Overscroll physics (`Compose/Foundation/Overscroll.lean`)

The rubber-band and spring-back math behind the translation-based
overscroll bounce at a scrollable's range ends. Android 12+ renders
overscroll as a GPU stretch (`EdgeEffect`), which the SDL backend cannot
express, and AOSP's own translation overfling is capped at
`ViewConfiguration.OVERFLING_DISTANCE` (6 px — visually nothing); the
model here is the one Compose itself ships where the stretch doesn't
exist: Compose Multiplatform's `CupertinoOverscrollEffect` (Apple's
rubber-band curve and spring constants).

Pure and `#guard`-tested; the integration (drag, release, fling-into-edge)
lives in `Compose/Foundation/Scroll.lean`.
-/

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

end Compose

end
