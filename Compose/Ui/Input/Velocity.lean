module

public section

namespace Compose

/-!
# Velocity tracking (`Compose/Ui/Input/Velocity.lean`)

A 1D pointer-velocity estimator for drag gestures: feed it the axis position
of each pointer sample, ask for the velocity at release to start a fling.
Mirrors `androidx.compose.ui.input.pointer.util.VelocityTracker1D` with
`Strategy.Impulse` — Compose's (and the Android platform's) default touch
strategy: consecutive segment slopes do "work" on the fling mass, so uniform
motion reproduces its slope exactly while an accelerating flick reads faster
than any least-squares fit would report (the property the strategy exists
for).

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

/-- Segments shorter than this contribute no slope: no digitizer samples
faster than 1 kHz, so a sub-ms dt is a stamping artifact whose division
would dominate the impulse with a garbage velocity. -/
def minSegmentNs : Float := 1e6

/-- The empty tracker (start of a gesture). -/
def empty : VelocityTracker := {}

/-- Record one sample, dropping samples outside `horizonNs` of it (and any
clock-skewed future ones) and capping at `maxSamples`. -/
def add (vt : VelocityTracker) (tNs : UInt64) (pos : Float32) : VelocityTracker :=
  let keep := vt.samples.filter fun (t, _) => t ≤ tNs && t + horizonNs ≥ tNs
  let keep := if keep.size ≥ maxSamples then keep.eraseIdx! 0 else keep
  ⟨keep.push (tNs, pos)⟩

/-- `sign(E)·√(2|E|)`: the (signed) speed of a unit mass with kinetic
energy `|E|` (androidx `kineticEnergyToVelocity`). -/
private def kineticEnergyToVelocity (e : Float) : Float :=
  (if e < 0 then -1.0 else 1.0) * (2.0 * e.abs).sqrt

/-- The estimated velocity at `nowNs`, px/second, via Android's impulse
strategy: over consecutive segments in chronological order,
`W += (vSeg − v(W))·|vSeg|` (halved after the oldest segment), and the
result is `v(W) = sign(W)·√(2|W|)`. Only samples within `restGapNs` of the
newest count — Compose's impulse window (its `previousSample` stays pinned
to the newest, so the 40 ms gap check measures age-from-newest; `horizonNs`
remains the retention bound in `add`). Zero when fewer than two samples
remain or the newest is `restGapNs` stale (the pointer was resting when
released). Segments shorter than `minSegmentNs` (equal-stamped bursts, or
near-coincident stamps from delivery-jittered batched forwarding) are
skipped, so they degrade gracefully instead of blowing up the slope —
dividing one frame of finger travel by a microsecond dt reads as a
hundreds-of-thousands px/s flick. -/
def velocity (vt : VelocityTracker) (nowNs : UInt64) : Float32 := Id.run do
  let past := vt.samples.filter fun (t, _) => t ≤ nowNs
  let some (newest, _) := past.back? | return 0
  if newest + restGapNs < nowNs then return 0
  let live := past.filter fun (t, _) => t + restGapNs ≥ newest
  if live.size < 2 then return 0
  -- Impulse in double precision, times in seconds relative to the oldest
  -- live sample.
  let t0 := live[0]!.1
  let pts := live.map fun (t, x) => ((t - t0).toFloat / 1e9, x.toFloat)
  let mut work : Float := 0
  for j in [1:pts.size] do
    let (tPrev, xPrev) := pts[j - 1]!
    let (tCur, xCur) := pts[j]!
    if (tCur - tPrev) * 1e9 < minSegmentNs then continue
    let vSeg := (xCur - xPrev) / (tCur - tPrev)
    work := work + (vSeg - kineticEnergyToVelocity work) * vSeg.abs
    if j == 1 then work := work * 0.5
  return (kineticEnergyToVelocity work).toFloat32

-- Uniform motion reproduces its slope: 32 px per 16 ms is 2000 px/s
-- (the work telescopes to v²/2 and √(2·v²/2) reads it back).
#guard
  ((VelocityTracker.empty
    |>.add 0 0 |>.add 16_000_000 32 |>.add 32_000_000 64
    |>.velocity 32_000_000) - 2000).abs < 0.01
-- Direction: decreasing positions give the negative velocity.
#guard
  ((VelocityTracker.empty
    |>.add 0 64 |>.add 16_000_000 32 |>.add 32_000_000 0
    |>.velocity 32_000_000) + 2000).abs < 0.01
-- A resting pointer (no motion) has zero velocity.
#guard
  (VelocityTracker.empty
    |>.add 0 42 |>.add 16_000_000 42 |>.add 32_000_000 42
    |>.velocity 32_000_000) == 0
-- A release ≥ `restGapNs` after the last move means the pointer stopped.
#guard
  (VelocityTracker.empty
    |>.add 0 0 |>.add 16_000_000 32
    |>.velocity (16_000_000 + restGapNs + 1)) == 0
-- Samples older than `restGapNs` before the newest do not contaminate the
-- estimate: an old fast segment followed by fresh uniform motion reports
-- only the fresh slope.
#guard
  ((VelocityTracker.empty
    |>.add 0 1000 |>.add 50_000_000 0 |>.add 66_000_000 32 |>.add 82_000_000 64
    |>.velocity 82_000_000) - 2000).abs < 0.01
-- The flick boost: an accelerating gesture (segments at 1000 then
-- 2000 px/s) reads above both the mean slope (1500) and the last segment —
-- work = 1000²/2 + (2000−1000)·2000 = 2.5e6, v = √(5e6) ≈ 2236.07.
#guard
  ((VelocityTracker.empty
    |>.add 0 0 |>.add 16_000_000 16 |>.add 32_000_000 48
    |>.velocity 32_000_000) - 2236.068).abs < 0.5
-- Equal-timestamp segments are skipped, not divided by: a same-stamped
-- burst (SDL forwarding batched samples without timestamps) keeps the
-- timed segments' estimate.
#guard
  ((VelocityTracker.empty
    |>.add 0 0 |>.add 16_000_000 32 |>.add 16_000_000 32 |>.add 32_000_000 64
    |>.velocity 32_000_000) - 2000).abs < 0.01
-- Sub-ms segments are stamping artifacts, skipped the same way: 16 px in
-- 50 µs would read as a 320k px/s flick and dominate the impulse
-- (regression: delivery-jittered batched touch produced 400k px/s
-- releases). Surviving segments: 2000 px/s (halved first), then
-- 16/0.01595 ≈ 1003 px/s → v = √(2·(2e6 + (1003−2000)·1003)) ≈ 1414.
#guard
  ((VelocityTracker.empty
    |>.add 0 0 |>.add 16_000_000 32 |>.add 16_050_000 48 |>.add 32_000_000 64
    |>.velocity 32_000_000) - 1414.2).abs < 20
#guard
  (VelocityTracker.empty
    |>.add 16_000_000 0 |>.add 16_000_000 32
    |>.velocity 16_000_000) == 0
-- Fewer than two samples: no estimate.
#guard (VelocityTracker.empty |>.velocity 0) == 0
#guard (VelocityTracker.empty |>.add 0 10 |>.velocity 0) == 0

end VelocityTracker

end Compose

end
