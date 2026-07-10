import Compose.Animation.Spec
import Compose.Runtime.State
import Compose.Runtime.Scheduler

namespace Compose

/-!
# Animatable (`Compose/Animation/Animatable.lean`)

A value holder that animates toward targets frame by frame on the
cooperative scheduler, mirroring
`androidx.compose.animation.core.Animatable`:

- `animateTo` is a `UiTask`: it subscribes to the frame clock
  (`UiTask.awaitFrame`) and writes `value` (an observable `MutableState`)
  every frame until the spec's duration elapses, then snaps to the exact
  target.
- **Interruption**: starting a new `animateTo`/`snapTo`/`stop` bumps an
  internal generation counter; the in-flight frame loop notices the stale
  generation at its next frame and stops without touching any state — and
  the new animation reads the *current* value **and** the current velocity
  vector as its initial conditions, Compose's `MutatorMutex` +
  velocity-carry-over semantics.
- Velocity is reset to zero when an animation ends normally
  (`endAnimation` in Compose) — it only carries across an *interruption*.
- Bounds (`updateBounds`): each frame's value is clamped per dimension;
  hitting a bound stops the animation at the clamped value (Compose's
  `BoundReached`).

`animateDecay` (fling) is intentionally omitted — nothing in the 7GUIs
demos flings (documented cut).

Cancelling the *coroutine* running `animateTo` (e.g. a `LaunchedEffect`
leaving composition) stops the frame loop at its next suspension point but
runs no epilogue (`UiTask` cancellation is exception-free), so `isRunning`
can remain `true` on an Animatable nothing references anymore — harmless,
but noted (Compose runs a `finally` there).
-/

/-- An animatable value holder: observable current value, target, running
flag, and a velocity vector that carries across interruptions. Mirrors
`androidx.compose.animation.core.Animatable`. -/
structure Animatable (α : Type) where
  /-- Endpoint/velocity conversion. Mirrors the `TwoWayConverter` argument. -/
  conv : VectorConverter α
  /-- The current value, written every animation frame (observable). Mirrors
  `Animatable.value`. -/
  value : MutableState α
  /-- The target of the latest `animateTo`/`snapTo` (observable). Mirrors
  `Animatable.targetValue`. -/
  targetValue : MutableState α
  /-- Whether an animation is in flight (observable). Mirrors
  `Animatable.isRunning`. -/
  isRunning : MutableState Bool
  /-- Current velocity in units/second per dimension. Mirrors
  `Animatable.velocityVector`. -/
  velocityVec : IO.Ref AnimationVector
  /-- Interruption counter: each `animateTo`/`snapTo`/`stop` bumps it; a
  frame loop holding a stale generation exits silently. -/
  generation : IO.Ref Nat
  /-- Per-dimension lower clamp. Mirrors `Animatable.lowerBound`. -/
  lowerBound : IO.Ref (Option AnimationVector)
  /-- Per-dimension upper clamp. Mirrors `Animatable.upperBound`. -/
  upperBound : IO.Ref (Option AnimationVector)

instance [Nonempty α] : Nonempty (Animatable α) :=
  ⟨{ conv := Classical.choice inferInstance
     value := Classical.choice inferInstance
     targetValue := Classical.choice inferInstance
     isRunning := Classical.choice inferInstance
     velocityVec := Classical.choice inferInstance
     generation := Classical.choice inferInstance
     lowerBound := Classical.choice inferInstance
     upperBound := Classical.choice inferInstance }⟩

namespace Animatable

/-- Create an `Animatable` resting at `initial`. Mirrors
`Animatable(initialValue, typeConverter)`. -/
def create [BEq α] (initial : α) (conv : VectorConverter α) : IO (Animatable α) := do
  let vec := conv.toVector initial
  return { conv
           value := ← MutableState.create initial
           targetValue := ← MutableState.create initial
           isRunning := ← MutableState.create false
           velocityVec := ← IO.mkRef (AnimationVector.zero vec.dim)
           generation := ← IO.mkRef 0
           lowerBound := ← IO.mkRef none
           upperBound := ← IO.mkRef none }

/-- The current velocity vector (units/second). Mirrors
`Animatable.velocityVector`. -/
def velocityVector (a : Animatable α) : IO AnimationVector :=
  a.velocityVec.get

/-- Read the current value *without* registering an observer (internal reads
and tests; composables should read `value` normally). -/
def peek (a : Animatable α) : IO α :=
  a.value.cell.get

/-- Clamp `v` into the bounds; `true` iff any dimension was clamped. -/
private def clampToBounds (a : Animatable α) (v : AnimationVector) :
    IO (AnimationVector × Bool) := do
  let lo? ← a.lowerBound.get
  let hi? ← a.upperBound.get
  let clamped := v.values.mapIdx fun i x =>
    let x := match lo? with | some lo => max x (lo.get i) | none => x
    match hi? with | some hi => min x (hi.get i) | none => x
  return (⟨clamped⟩, AnimationVector.mk clamped != v)

/-- Bump the generation, telling any in-flight frame loop to stand down at
its next frame. Returns the new generation. -/
private def interrupt (a : Animatable α) : IO Nat :=
  a.generation.modifyGet fun g => (g + 1, g + 1)

/-- End-of-animation bookkeeping shared by completion, bound hits, `stop`,
and `snapTo`: velocity resets to zero (Compose's `endAnimation`). -/
private def endAnimation (a : Animatable α) : IO Unit := do
  a.velocityVec.set (AnimationVector.zero (← a.velocityVec.get).dim)
  a.isRunning.set false

/-- The per-frame loop of `animateTo`; exits silently when the generation
went stale (interruption) and is dropped by the scheduler on `Job.cancel`. -/
private partial def frameLoop [BEq α] (a : Animatable α) (myGen : Nat)
    (spec : AnimationSpec α) (startVec targetVec v0 : AnimationVector)
    (dur? : Option UInt64) (t0 : UInt64) : UiTask Unit := do
  let ns ← UiTask.awaitFrame
  if (← a.generation.get) != myGen then return
  let play := if ns ≤ t0 then 0 else ns - t0
  if dur?.any (play ≥ ·) then
    -- Finished: exact target (clamped), velocity zero.
    let (clamped, _) ← a.clampToBounds targetVec
    a.endAnimation
    a.value.set (a.conv.fromVector clamped)
    a.targetValue.set (a.conv.fromVector clamped)
  else
    let v := spec.valueAt a.conv play startVec targetVec v0
    let vel := spec.velocityAt a.conv play startVec targetVec v0
    let (clamped, hitBound) ← a.clampToBounds v
    if hitBound then
      -- Compose's `BoundReached`: settle at the bound and stop.
      a.endAnimation
      a.value.set (a.conv.fromVector clamped)
    else
      a.velocityVec.set vel
      a.value.set (a.conv.fromVector clamped)
      frameLoop a myGen spec startVec targetVec v0 dur? t0

/-- Animate from the current value (and current velocity — carried over from
any interrupted animation) to `target`, writing `value` every frame; returns
when the animation finishes or is superseded. Starting a new
`animateTo`/`snapTo` interrupts the in-flight one. Mirrors
`Animatable.animateTo(targetValue, animationSpec)`. -/
def animateTo [BEq α] (a : Animatable α) (target : α)
    (spec : AnimationSpec α := .spring) : UiTask Unit := do
  let myGen ← a.interrupt
  let startVal ← a.peek
  let v0 ← a.velocityVec.get
  a.targetValue.set target
  a.isRunning.set true
  let startVec := a.conv.toVector startVal
  let targetVec := a.conv.toVector target
  let dur? := spec.durationNs a.conv startVec targetVec v0
  let t0 ← UiTask.awaitFrame
  if (← a.generation.get) != myGen then return
  frameLoop a myGen spec startVec targetVec v0 dur? t0

/-- Interrupt any in-flight animation and set the value immediately (clamped
to the bounds); velocity resets to zero. Mirrors `Animatable.snapTo`. -/
def snapTo [BEq α] (a : Animatable α) (target : α) : IO Unit := do
  let _ ← a.interrupt
  let (clamped, _) ← a.clampToBounds (a.conv.toVector target)
  a.endAnimation
  let v := a.conv.fromVector clamped
  a.targetValue.set v
  a.value.set v

/-- Interrupt any in-flight animation, keeping the current value; velocity
resets to zero. Mirrors `Animatable.stop`. -/
def stop (a : Animatable α) : IO Unit := do
  let _ ← a.interrupt
  a.endAnimation

/-- Set per-dimension bounds (`none` = unbounded); the current value is
clamped into them immediately. Mirrors `Animatable.updateBounds`. -/
def updateBounds [BEq α] (a : Animatable α)
    (lower : Option α := none) (upper : Option α := none) : IO Unit := do
  a.lowerBound.set (lower.map a.conv.toVector)
  a.upperBound.set (upper.map a.conv.toVector)
  let (clamped, hit) ← a.clampToBounds (a.conv.toVector (← a.peek))
  if hit then a.value.set (a.conv.fromVector clamped)

end Animatable

end Compose
