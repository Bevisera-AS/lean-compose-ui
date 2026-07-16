module

public section

namespace Compose

/-!
# Velocity tracking (`Compose/Ui/Input/Velocity.lean`)

A 1D pointer-velocity estimator for drag gestures: feed it the axis position
of each pointer sample, ask for the velocity at release to start a fling.
Mirrors `androidx.compose.ui.input.pointer.util.VelocityTracker1D`
(the least-squares strategy, degree 1): the velocity is the slope of the
best-fit line through the samples of the last `horizonNs`, so it smooths
jittery move events instead of amplifying the last two.

Pure and allocation-light (an `Array` of pairs, capped) — the estimator math
is `#guard`-tested below; the integration lives in the drag-scroll handler
(`Compose/Foundation/Scroll.lean`).
-/

/-- Recent pointer samples on one axis, oldest first. Feed with `add`, read
with `velocity`. -/
structure VelocityTracker where
  /-- `(timestamp ns, axis position px)` samples within `horizonNs` of the
  newest, oldest first. -/
  samples : Array (UInt64 × Float32) := #[]
  deriving Inhabited

namespace VelocityTracker

/-- Samples older than this (relative to the newest) are ignored: velocity
reflects the *current* motion, not the whole gesture. -/
def horizonNs : UInt64 := 100_000_000

/-- Cap on retained samples (drag moves arrive per-frame; 20 covers the
horizon at 144 Hz). -/
def maxSamples : Nat := 20

/-- A release this long after the last move means the pointer had stopped:
the velocity is zero, not the stale pre-pause slope (Android's
"assume pointer stopped" rule). -/
def restGapNs : UInt64 := 40_000_000

/-- The empty tracker (start of a gesture). -/
def empty : VelocityTracker := {}

/-- Record one sample, dropping samples outside `horizonNs` of it (and any
clock-skewed future ones) and capping at `maxSamples`. -/
def add (vt : VelocityTracker) (tNs : UInt64) (pos : Float32) : VelocityTracker :=
  let keep := vt.samples.filter fun (t, _) => t ≤ tNs && t + horizonNs ≥ tNs
  let keep := if keep.size ≥ maxSamples then keep.eraseIdx! 0 else keep
  ⟨keep.push (tNs, pos)⟩

/-- The estimated velocity at `nowNs`, px/second: the least-squares slope
through the samples of the last `horizonNs`. Zero when fewer than two
samples remain or the newest is `restGapNs` stale (the pointer was resting
when released). -/
def velocity (vt : VelocityTracker) (nowNs : UInt64) : Float32 := Id.run do
  let live := vt.samples.filter fun (t, _) => t + horizonNs ≥ nowNs && t ≤ nowNs
  let some (newest, _) := live.back? | return 0
  if newest + restGapNs < nowNs then return 0
  if live.size < 2 then return 0
  -- Least squares in double precision, times in seconds relative to the
  -- oldest live sample (small exact values; ns → s is a power-of-two scale
  -- for the test inputs below).
  let t0 := live[0]!.1
  let pts := live.map fun (t, x) => ((t - t0).toFloat / 1e9, x.toFloat)
  let n := pts.size.toFloat
  let tMean := (pts.foldl (· + ·.1) (0 : Float)) / n
  let xMean := (pts.foldl (· + ·.2) (0 : Float)) / n
  let num := pts.foldl (fun a (t, x) => a + (t - tMean) * (x - xMean)) (0 : Float)
  let den := pts.foldl (fun a (t, _) => a + (t - tMean) * (t - tMean)) (0 : Float)
  if den == 0 then return 0
  return (num / den).toFloat32

-- Uniform motion: 125 px per 62.5 ms is exactly 2000 px/s.
#guard
  (VelocityTracker.empty
    |>.add 0 0 |>.add 62_500_000 125 |>.add 125_000_000 250
    |>.velocity 125_000_000) == 2000
-- Direction: decreasing positions give the negative slope.
#guard
  (VelocityTracker.empty
    |>.add 0 250 |>.add 62_500_000 125 |>.add 125_000_000 0
    |>.velocity 125_000_000) == -2000
-- A resting pointer (no motion) has zero velocity.
#guard
  (VelocityTracker.empty
    |>.add 0 42 |>.add 62_500_000 42 |>.add 125_000_000 42
    |>.velocity 125_000_000) == 0
-- A release ≥ `restGapNs` after the last move means the pointer stopped.
#guard
  (VelocityTracker.empty
    |>.add 0 0 |>.add 62_500_000 125
    |>.velocity (62_500_000 + restGapNs + 1)) == 0
-- Samples beyond the horizon do not contaminate the estimate: an old fast
-- segment followed by fresh uniform motion reports only the fresh slope.
#guard
  (VelocityTracker.empty
    |>.add 0 1000 |>.add 500_000_000 0 |>.add 562_500_000 125
    |>.velocity 562_500_000) == 2000
-- Fewer than two samples: no estimate.
#guard (VelocityTracker.empty |>.velocity 0) == 0
#guard (VelocityTracker.empty |>.add 0 10 |>.velocity 0) == 0

end VelocityTracker

end Compose

end
