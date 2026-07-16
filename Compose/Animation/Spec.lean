module

public import Compose.Animation.Easing
public meta import Compose.Animation.Easing
public import Compose.Animation.Vector
public meta import Compose.Animation.Vector
public import Compose.Animation.Spring
public meta import Compose.Animation.Spring

public section

namespace Compose

/-!
# Animation specs (`Compose/Animation/Spec.lean`)

`AnimationSpec` describes *how* a value animates toward a target; evaluation
is vectorized: the caller converts endpoints through a `VectorConverter` and
the spec animates each `Float32` dimension, mirroring
`androidx.compose.animation.core.AnimationSpec` +
`VectorizedAnimationSpec`. Play time is nanoseconds from the animation's
start frame; velocities are units per second.

Notes on fidelity:
- Tween/keyframe velocity is the 1 ms finite difference Compose uses
  (`VectorizedDurationBasedAnimationSpec.getVelocityFromNanos`); spring
  velocity is closed-form.
- A spring's duration is *until settled* (value and velocity under
  threshold). Compose estimates it with `SpringEstimation`; we step the
  closed form at 1 ms granularity, capped at 10 s (documented deviation —
  same observable result at frame granularity).
- In reversed repeat iterations the reported velocity is negated (the value
  curve runs backwards in time), matching the physical derivative.
-/

/-- What a repeating spec does when one iteration ends. Mirrors
`androidx.compose.animation.core.RepeatMode`. -/
inductive RepeatMode where
  /-- Jump back to the start. -/
  | restart
  /-- Play the next iteration backwards. -/
  | reverse
  deriving Repr, BEq, Inhabited

/-- Specification of an animation from a start to a target value. Mirrors
`androidx.compose.animation.core.AnimationSpec` (`TweenSpec`, `SpringSpec`,
`KeyframesSpec`, `RepeatableSpec`, `InfiniteRepeatableSpec`, `SnapSpec`). -/
inductive AnimationSpec (α : Type) where
  /-- Fixed-duration interpolation through `easing`. Mirrors `tween`. -/
  | tween (durationMs : Nat := 300) (delayMs : Nat := 0)
          (easing : Easing := .fastOutSlowIn)
  /-- Physics-based spring; runs until value *and* velocity settle under
  `visibilityThreshold` (default `0.01` per dimension). Mirrors `spring`. -/
  | spring (dampingRatio : Float32 := Spring.dampingRatioNoBouncy)
           (stiffness : Float32 := Spring.stiffnessMedium)
           (visibilityThreshold : Option α := none)
  /-- Values pinned at millisecond timestamps; segments interpolate with the
  easing attached to the keyframe the segment *starts* at. A frame at `0` /
  `durationMs` overrides the start / target value. Mirrors `keyframes`. -/
  | keyframes (durationMs : Nat) (frames : List (Nat × α × Easing) := [])
              (delayMs : Nat := 0)
  /-- Play `inner` `iterations` times (≥ 1). Mirrors `repeatable`. -/
  | repeatable (iterations : Nat) (inner : AnimationSpec α)
               (mode : RepeatMode := .restart)
  /-- Repeat `inner` forever. Mirrors `infiniteRepeatable`. -/
  | infiniteRepeatable (inner : AnimationSpec α) (mode : RepeatMode := .restart)
  /-- Jump straight to the target after `delayMs`. Mirrors `snap`. -/
  | snap (delayMs : Nat := 0)

instance : Inhabited (AnimationSpec α) := ⟨.tween⟩

namespace AnimationSpec

/-- Milliseconds → nanoseconds (the spec time unit → the frame-clock unit). -/
def msToNs (ms : Nat) : UInt64 := ms.toUInt64 * 1_000_000

/-- Saturating subtraction (play times never go negative). -/
private def satSub (a b : UInt64) : UInt64 := if a ≤ b then 0 else a - b

private def nsToSec (ns : UInt64) : Float32 := (ns.toFloat / 1e9).toFloat32

#guard satSub 5 7 == 0
#guard satSub 7 5 == 2
#guard msToNs 300 == 300_000_000

/-- Whether the spec never finishes on its own. -/
def isInfinite : AnimationSpec α → Bool
  | .infiniteRepeatable .. => true
  | .repeatable _ inner _ => inner.isInfinite
  | _ => false

/-- Per-dimension settling thresholds for a spring: the converted
`visibilityThreshold`, or `0.01` everywhere. -/
private def springThresholds (conv : VectorConverter α)
    (threshold? : Option α) (dims : Nat) : AnimationVector :=
  match threshold? with
  | some t => (conv.toVector t).map (fun x =>
      if x.abs > 0 then x.abs else Spring.defaultDisplacementThreshold)
  | none => ⟨.replicate dims Spring.defaultDisplacementThreshold⟩

/-- Spring-duration search cap: 10 s of stepping at 1 ms. -/
private def springDurationCapMs : Nat := 10_000

/-- First 1 ms step at which every dimension of the spring is settled
(value under threshold, velocity under `threshold × 62.5`/s), capped at
`springDurationCapMs`. Stands in for Compose's `SpringEstimation` closed-form
bound (documented deviation, see the module docstring). -/
private def springDurationNs (ζ k : Float32) (thresholds : AnimationVector)
    (start target v0 : AnimationVector) : UInt64 := Id.run do
  for ms in [0 : springDurationCapMs + 1] do
    let t := (ms.toFloat / 1000).toFloat32
    let settled := (List.range start.dim).all fun i =>
      let (v, vel) := Spring.evaluate ζ k (start.get i) (target.get i) (v0.get i) t
      Spring.isAtEquilibrium (target.get i) (thresholds.get i) v vel
    if settled then return msToNs ms
  return msToNs springDurationCapMs

/-- Total run time in nanoseconds (including delay), or `none` for infinite
specs. Springs report their until-settled time for the given endpoints and
start velocity. Mirrors `VectorizedAnimationSpec.getDurationNanos`. -/
def durationNs (spec : AnimationSpec α) (conv : VectorConverter α)
    (start target v0 : AnimationVector) : Option UInt64 :=
  match spec with
  | .tween d delay _ => some (msToNs (d + delay))
  | .keyframes d _ delay => some (msToNs (d + delay))
  | .snap delay => some (msToNs delay)
  | .spring ζ k thr? =>
    some (springDurationNs ζ k (springThresholds conv thr? start.dim) start target v0)
  | .repeatable iters inner mode =>
    let _ := mode
    (durationNs inner conv start target v0).map (· * (max 1 iters).toUInt64)
  | .infiniteRepeatable .. => none

/-- Keyframe points of a `keyframes` spec, sorted by time, with implicit
`(0, start)` / `(durNs, target)` endpoints unless overridden by a frame. -/
private def keyframePoints (conv : VectorConverter α) (durMs : Nat)
    (frames : List (Nat × α × Easing)) (start target : AnimationVector) :
    Array (UInt64 × AnimationVector × Easing) :=
  let user := frames.filter (·.1 ≤ durMs) |>.toArray
    |>.map (fun (ms, v, e) => (msToNs ms, conv.toVector v, e))
    |>.qsort (·.1 < ·.1)
  let withStart :=
    if user.any (·.1 == 0) then user
    else #[((0 : UInt64), start, Easing.linear)] ++ user
  if withStart.any (·.1 == msToNs durMs) then withStart
  else withStart.push (msToNs durMs, target, Easing.linear)

/-- The repeat-iteration index for `playNs` (capped for finite repeats). -/
private def repeatCount (durNs : UInt64) (iters? : Option Nat) (playNs : UInt64) :
    UInt64 :=
  let raw := playNs / durNs
  match iters? with
  | some n => min raw ((max 1 n).toUInt64 - 1)
  | none => raw

/-- Local play time inside the current iteration, with reverse iterations
mirrored. Mirrors `VectorizedRepeatableSpec.repetitionPlayTimeNanos`. -/
private def repeatLocalNs (durNs : UInt64) (iters? : Option Nat)
    (mode : RepeatMode) (playNs : UInt64) : UInt64 :=
  if durNs == 0 then 0 else
  let count := repeatCount durNs iters? playNs
  let localNs := min (satSub playNs (count * durNs)) durNs
  match mode with
  | .restart => localNs
  | .reverse => if count % 2 == 1 then durNs - localNs else localNs

#guard repeatLocalNs 100 none .restart 250 == 50
#guard repeatLocalNs 100 none .reverse 250 == 50
#guard repeatLocalNs 100 none .reverse 120 == 80
#guard repeatLocalNs 100 (some 3) .restart 450 == 100  -- capped at the last iteration's end
#guard repeatLocalNs 100 (some 2) .reverse 250 == 0    -- clamped at the reversed end = start

mutual

/-- The animated vector at `playNs` nanoseconds after the animation start.
Mirrors `VectorizedAnimationSpec.getValueFromNanos`. -/
partial def valueAt (spec : AnimationSpec α) (conv : VectorConverter α)
    (playNs : UInt64) (start target v0 : AnimationVector) : AnimationVector :=
  match spec with
  | .tween d delay easing =>
    let durNs := msToNs d
    let localNs := min (satSub playNs (msToNs delay)) durNs
    let fraction :=
      if durNs == 0 then 1.0
      else (localNs.toFloat / durNs.toFloat).toFloat32
    .lerp start target (easing.transform fraction)
  | .snap delay => if playNs < msToNs delay then start else target
  | .spring ζ k _ =>
    let t := nsToSec playNs
    ⟨start.values.mapIdx fun i s =>
      (Spring.evaluate ζ k s (target.get i) (v0.get i) t).1⟩
  | .keyframes d frames delay =>
    let durNs := msToNs d
    let pts := keyframePoints conv d frames start target
    let localNs := min (satSub playNs (msToNs delay)) durNs
    Id.run do
      let mut i := 0
      for j in [0 : pts.size] do
        if pts[j]!.1 ≤ localNs then i := j
      let (t0, v0', e) := pts[i]!
      if h : i + 1 < pts.size then
        let (t1, v1, _) := pts[i + 1]
        let frac := ((localNs - t0).toFloat / (t1 - t0).toFloat).toFloat32
        return .lerp v0' v1 (e.transform frac)
      else
        return v0'
  | .repeatable iters inner mode =>
    match durationNs inner conv start target v0 with
    | none => valueAt inner conv playNs start target v0
    | some durNs =>
      valueAt inner conv (repeatLocalNs durNs (some iters) mode playNs)
        start target (repeatV0 inner conv durNs playNs start target v0)
  | .infiniteRepeatable inner mode =>
    match durationNs inner conv start target v0 with
    | none => valueAt inner conv playNs start target v0
    | some durNs =>
      valueAt inner conv (repeatLocalNs durNs none mode playNs)
        start target (repeatV0 inner conv durNs playNs start target v0)

/-- The velocity vector (units/second) at `playNs`. Closed form for springs;
Compose's 1 ms finite difference for duration-based specs; negated in
reversed repeat iterations. Mirrors
`VectorizedAnimationSpec.getVelocityFromNanos`. -/
partial def velocityAt (spec : AnimationSpec α) (conv : VectorConverter α)
    (playNs : UInt64) (start target v0 : AnimationVector) : AnimationVector :=
  match spec with
  | .spring ζ k _ =>
    let t := nsToSec playNs
    ⟨start.values.mapIdx fun i s =>
      (Spring.evaluate ζ k s (target.get i) (v0.get i) t).2⟩
  | .snap _ => v0
  | .tween d delay _ =>
    finiteDiff spec conv playNs start target v0 (msToNs delay) (msToNs (d + delay))
  | .keyframes d _ delay =>
    finiteDiff spec conv playNs start target v0 (msToNs delay) (msToNs (d + delay))
  | .repeatable iters inner mode =>
    match durationNs inner conv start target v0 with
    | none => velocityAt inner conv playNs start target v0
    | some durNs =>
      let count := repeatCount durNs (some iters) playNs
      let vel := velocityAt inner conv (repeatLocalNs durNs (some iters) mode playNs)
        start target (repeatV0 inner conv durNs playNs start target v0)
      if mode == .reverse && count % 2 == 1 then vel.map (- ·) else vel
  | .infiniteRepeatable inner mode =>
    match durationNs inner conv start target v0 with
    | none => velocityAt inner conv playNs start target v0
    | some durNs =>
      let count := repeatCount durNs none playNs
      let vel := velocityAt inner conv (repeatLocalNs durNs none mode playNs)
        start target (repeatV0 inner conv durNs playNs start target v0)
      if mode == .reverse && count % 2 == 1 then vel.map (- ·) else vel

/-- Start velocity for the current repeat iteration: the caller's `v0` in the
first, the inner spec's end velocity afterwards. Mirrors
`VectorizedRepeatableSpec.repetitionStartVelocity`. -/
private partial def repeatV0 (inner : AnimationSpec α) (conv : VectorConverter α)
    (durNs playNs : UInt64) (start target v0 : AnimationVector) : AnimationVector :=
  if playNs > durNs then velocityAt inner conv durNs start target v0 else v0

/-- Velocity of a duration-based spec by Compose's 1 ms backward difference,
with the sample window clamped into `[delayNs, endNs]`. -/
private partial def finiteDiff (spec : AnimationSpec α) (conv : VectorConverter α)
    (playNs : UInt64) (start target v0 : AnimationVector)
    (delayNs endNs : UInt64) : AnimationVector :=
  let t1 := min (max playNs delayNs) endNs
  let t0 := max (satSub t1 (msToNs 1)) delayNs
  if t1 == t0 then .zero start.dim
  else
    let dtSec := nsToSec (t1 - t0)
    (valueAt spec conv t1 start target v0).zipWith
      (fun a b => (a - b) / dtSec) (valueAt spec conv t0 start target v0)

end

/-! ## Guards (float specs through `VectorConverter.float32`) -/

private def fconv : VectorConverter Float32 := .float32

/-- Float value of a float spec at `ms` (start 0, target 10, `v0` per-second). -/
private def fval (spec : AnimationSpec Float32) (ms : Nat) (v0 : Float32 := 0) : Float32 :=
  (spec.valueAt fconv (msToNs ms) (.v1 0) (.v1 10) (.v1 v0)).get 0

/-- Float velocity (units/second) of a float spec at `ms`. -/
private def fvel (spec : AnimationSpec Float32) (ms : Nat) (v0 : Float32 := 0) : Float32 :=
  (spec.velocityAt fconv (msToNs ms) (.v1 0) (.v1 10) (.v1 v0)).get 0

private def linTween (d : Nat) (delay : Nat := 0) : AnimationSpec Float32 :=
  .tween d delay .linear

-- tween endpoints, midpoint, clamping past the end
#guard fval (linTween 100) 0 == 0
#guard fval (linTween 100) 50 == 5
#guard fval (linTween 100) 100 == 10
#guard fval (linTween 100) 250 == 10
-- delay holds the start value, then the timeline shifts
#guard fval (linTween 100 (delay := 50)) 25 == 0
#guard Easing.approx (fval (linTween 100 (delay := 50)) 100) 5
-- easing applies to the time fraction
#guard Easing.approx (fval (.tween 100 0 .fastOutSlowIn) 50) 7.756 (tol := 0.01)
-- linear tween velocity ≈ span/duration; zero during the delay and after the end
#guard Easing.approx (fvel (linTween 100) 50) 100 (tol := 0.01)
#guard fvel (linTween 100 (delay := 50)) 20 == 0
-- past the end, the clamped sample window reports the end slope (Compose clamps too)
#guard Easing.approx (fvel (linTween 100) 300) 100 (tol := 0.01)
-- zero-duration tween lands immediately
#guard fval (linTween 0) 0 == 10
-- snap: start before the delay, target at/after; duration = delay
#guard fval (.snap 10) 5 == 0
#guard fval (.snap 10) 10 == 10
#guard fvel (.snap 10) 5 (v0 := 3) == 3
#guard (AnimationSpec.snap (α := Float32) 10).durationNs fconv (.v1 0) (.v1 10) (.v1 0)
        == some (msToNs 10)

-- keyframes: interpolation at and between frames, easing-out per keyframe
private def kf : AnimationSpec Float32 :=
  .keyframes 200 [(50, 2, .linear), (100, 6, .linear)]
#guard fval kf 0 == 0
#guard fval kf 25 == 1        -- 0 → 2 over [0, 50]
#guard fval kf 50 == 2        -- pinned
#guard fval kf 75 == 4        -- 2 → 6 over [50, 100]
#guard fval kf 100 == 6
#guard fval kf 150 == 8       -- 6 → 10 over [100, 200]
#guard fval kf 200 == 10
#guard fval kf 999 == 10
#guard Easing.approx (fvel kf 75) 80 (tol := 0.01)   -- (6−2)/50ms
-- a frame at 0 overrides the start segment's easing
#guard Easing.approx
  (fval (.keyframes 100 [(0, 0, .fastOutSlowIn)]) 50) 7.756 (tol := 0.01)

-- spring value/velocity agree with the closed form; duration is until-settled
private def sspring : AnimationSpec Float32 := .spring 0.2 100 (some 0.01)
#guard fval sspring 0 == 0
#guard fvel sspring 0 (v0 := 5) == 5
#guard fval sspring 321 > 13    -- underdamped 0→10 overshoots ~15.3 at t = π/ω_d
#guard (sspring.durationNs fconv (.v1 0) (.v1 10) (.v1 0)).isSome
#guard ((sspring.durationNs fconv (.v1 0) (.v1 10) (.v1 0)).getD 0) > msToNs 1000
-- already settled → zero duration
#guard (AnimationSpec.spring (α := Float32) 1.0 1500 none).durationNs fconv
        (.v1 5) (.v1 5) (.v1 0) == some 0
-- critically damped spring value settles at its reported duration
private def critDur : UInt64 :=
  ((AnimationSpec.spring (α := Float32) 1.0 400 none).durationNs fconv
    (.v1 0) (.v1 10) (.v1 0)).getD 0
#guard Easing.approx (fval (.spring 1.0 400 none) (critDur / 1_000_000).toNat) 10 (tol := 0.02)

-- repeatable restart vs reverse; reverse mirrors within the odd iterations
private def rep3 (mode : RepeatMode) : AnimationSpec Float32 :=
  .repeatable 3 (linTween 100) mode
#guard fval (rep3 .restart) 80 == 8
#guard fval (rep3 .restart) 120 == 2
#guard fval (rep3 .reverse) 120 == 8    -- mirrored: 100−20
#guard fval (rep3 .reverse) 170 == 3
#guard fval (rep3 .reverse) 250 == 5    -- third iteration forward again
#guard fval (rep3 .reverse) 300 == 10   -- ends at the target (odd count)
#guard fval (rep3 .restart) 999 == 10   -- clamped at the total end
#guard (rep3 .restart).durationNs fconv (.v1 0) (.v1 10) (.v1 0) == some (msToNs 300)
-- velocity flips sign in reversed iterations
#guard Easing.approx (fvel (rep3 .restart) 120) 100 (tol := 0.01)
#guard Easing.approx (fvel (rep3 .reverse) 120) (-100) (tol := 0.01)
-- infinite specs report no duration and keep cycling
#guard (AnimationSpec.infiniteRepeatable (linTween 100) .reverse).isInfinite
#guard !(rep3 .reverse).isInfinite
#guard (AnimationSpec.infiniteRepeatable (linTween 100) .reverse).durationNs fconv
        (.v1 0) (.v1 10) (.v1 0) == none
#guard fval (.infiniteRepeatable (linTween 100) .reverse) 320 == 8
#guard fval (.infiniteRepeatable (linTween 100) .restart) 320 == 2
#guard fval (.infiniteRepeatable (linTween 100) .reverse) 1050 == 5

end AnimationSpec

end Compose

end
