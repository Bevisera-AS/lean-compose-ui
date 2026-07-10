import Compose.Animation.AnimateAsState

namespace Compose

/-!
# Transition (`Compose/Animation/Transition.lean`)

State-driven, multi-property animation, mirroring
`androidx.compose.animation.core.Transition` / `updateTransition`:

- `updateTransition targetState` remembers a `Transition` and retargets it
  when `targetState` changes. Following Compose's `updateTarget`, the new
  segment starts at the previous *target* state (`currentState` jumps there
  even if it was never visually reached), so `Segment = (prevTarget,
  newTarget)`.
- Each `animateFloat/Dp/Color/Value` property owns an `Animatable`;
  retargeting mid-flight interrupts it with velocity carry-over.
- `currentState` becomes `targetState` (and `isRunning` turns false) once
  **all** registered properties settle; properties leaving the composition
  deregister.
- `InfiniteTransition` (`rememberInfiniteTransition`) runs its properties
  for as long as they are composed, unsubscribing from the frame clock when
  they leave.
-/

/-- A pending (or completed) state change of a `Transition`, passed to
`transitionSpec` so different state pairs can animate differently. Mirrors
`androidx.compose.animation.core.Transition.Segment`. -/
structure Transition.Segment (σ : Type) where
  /-- The state the transition started from. -/
  initialState : σ
  /-- The state the transition is heading to. -/
  targetState : σ
  deriving Repr, BEq

/-- Whether this segment goes `initial → target`. Mirrors
`Segment.isTransitioningTo` (Compose's infix form). -/
def Transition.Segment.isTransitioningTo [BEq σ] (s : Transition.Segment σ)
    (initial target : σ) : Bool :=
  s.initialState == initial && s.targetState == target

/-- One animated property registered on a `Transition` (settle tracking). -/
structure TransitionProp where
  id : Nat
  /-- `false` while the property's animation is in flight. -/
  settled : IO.Ref Bool

instance : Nonempty TransitionProp :=
  ⟨{ id := 0, settled := Classical.choice inferInstance }⟩

/-- A state-driven transition: observable current/target states and running
flag, plus the registered animated properties. Mirrors
`androidx.compose.animation.core.Transition`. -/
structure Transition (σ : Type) where
  /-- The settled state; equals `targetState` when idle. Mirrors
  `Transition.currentState`. -/
  currentState : MutableState σ
  /-- The state being animated toward. Mirrors `Transition.targetState`. -/
  targetState : MutableState σ
  /-- Whether any property animation is in flight. Mirrors
  `Transition.isRunning`. -/
  isRunning : MutableState Bool
  /-- Animated properties currently composed. -/
  props : IO.Ref (Array TransitionProp)

instance [Nonempty σ] : Nonempty (Transition σ) :=
  ⟨{ currentState := Classical.choice inferInstance
     targetState := Classical.choice inferInstance
     isRunning := Classical.choice inferInstance
     props := Classical.choice inferInstance }⟩

namespace Transition

/-- Create a transition resting at `initial` (both states equal, idle). -/
def create [BEq σ] (initial : σ) : IO (Transition σ) :=
  return { currentState := ← MutableState.create initial
           targetState := ← MutableState.create initial
           isRunning := ← MutableState.create false
           props := ← IO.mkRef #[] }

/-- If every registered property has settled, finish the transition:
`currentState` becomes `targetState`, `isRunning` turns false. -/
def settleCheck (t : Transition σ) : IO Unit := do
  if ← (← t.props.get).allM (·.settled.get) then
    t.currentState.set (← t.targetState.cell.get)
    t.isRunning.set false

end Transition

/-- Remember a `Transition` tracking `targetState`: a change retargets every
property animation mid-flight (with velocity carry-over) and — following
Compose's `updateTarget` — starts the new segment at the previous target
state. Mirrors `androidx.compose.animation.core.updateTransition`. -/
def updateTransition [BEq σ] (targetState : σ) : Composable (Transition σ) := do
  have : Nonempty σ := ⟨targetState⟩
  let t ← remember (Transition.create targetState)
  let prev ← t.targetState.cell.get
  if prev != targetState then
    liftM (m := IO) do
      -- "Starting state should be the next state": segments begin at the
      -- previous target, even when it was never reached.
      t.currentState.set prev
      t.targetState.set targetState
      -- No properties → nothing will animate; settle immediately.
      if (← t.props.get).isEmpty then
        t.currentState.set targetState
  return t

namespace Transition

/-- Animate one property of the transition: `targetValueOf` maps each state
to the property's value, `transitionSpec` picks the spec per segment. On a
target change the property re-animates from its current value and velocity.
Mirrors `Transition.animateValue`. -/
def animateValue [BEq σ] [BEq α] (t : Transition σ) (conv : VectorConverter α)
    (transitionSpec : Transition.Segment σ → AnimationSpec α := fun _ => .spring)
    (targetValueOf : σ → α) : Composable (State α) := do
  let tgtState ← t.targetState.get
  let newTarget := targetValueOf tgtState
  have : Nonempty α := ⟨newTarget⟩
  let anim ← remember (Animatable.create newTarget conv)
  let prop ← rememberObserved do
    let p : TransitionProp := { id := ← freshId, settled := ← IO.mkRef true }
    pure (p, { onRemembered := t.props.modify (·.push p)
               onForgotten := do
                 t.props.modify (·.filter (·.id != p.id))
                 t.settleCheck })
  -- Detect this property's target change during composition so `isRunning`
  -- flips synchronously with the retarget (the coroutine starts next frame).
  let lastTarget ← remember (IO.mkRef newTarget)
  if (← lastTarget.get) != newTarget then
    liftM (m := IO) do
      lastTarget.set newTarget
      prop.settled.set false
      t.isRunning.set true
  let segInitial ← t.currentState.cell.get
  LaunchedEffect tgtState do
    let resting := (← anim.peek) == newTarget && !(← anim.isRunning.cell.get)
    unless resting do
      anim.animateTo newTarget (transitionSpec ⟨segInitial, tgtState⟩)
    prop.settled.set true
    t.settleCheck
  return anim.value.asState

/-- `Float32` property. Mirrors `Transition.animateFloat`. -/
def animateFloat [BEq σ] (t : Transition σ)
    (transitionSpec : Transition.Segment σ → AnimationSpec Float32 := fun _ => .spring)
    (targetValueOf : σ → Float32) : Composable (State Float32) :=
  t.animateValue .float32 transitionSpec targetValueOf

/-- `Dp` property. Mirrors `Transition.animateDp`. -/
def animateDp [BEq σ] (t : Transition σ)
    (transitionSpec : Transition.Segment σ → AnimationSpec Dp := fun _ => .spring)
    (targetValueOf : σ → Dp) : Composable (State Dp) :=
  t.animateValue .dp transitionSpec targetValueOf

/-- `Color` property (sRGB channels, see `VectorConverter.color`). Mirrors
`Transition.animateColor`. -/
def animateColor [BEq σ] (t : Transition σ)
    (transitionSpec : Transition.Segment σ → AnimationSpec Color := fun _ => .spring)
    (targetValueOf : σ → Color) : Composable (State Color) :=
  t.animateValue .color transitionSpec targetValueOf

end Transition

/-- Host for animations that run for as long as they are composed. Mirrors
`androidx.compose.animation.core.InfiniteTransition`. -/
structure InfiniteTransition where
  private mk ::

instance : Nonempty InfiniteTransition := ⟨⟨⟩⟩

/-- Remember an `InfiniteTransition`. Mirrors
`androidx.compose.animation.core.rememberInfiniteTransition`. -/
def rememberInfiniteTransition : Composable InfiniteTransition :=
  return ⟨⟩

namespace InfiniteTransition

/-- The endless frame loop of one infinite property: evaluate the spec at
the play time and write the state; a (misused) finite spec parks at its end
value and unsubscribes. -/
private partial def infLoop [BEq α] (st : MutableState α) (conv : VectorConverter α)
    (spec : AnimationSpec α) (startVec targetVec v0 : AnimationVector)
    (dur? : Option UInt64) (t0 : UInt64) : UiTask Unit := do
  let ns ← UiTask.awaitFrame
  let play := if ns ≤ t0 then 0 else ns - t0
  st.set (conv.fromVector (spec.valueAt conv play startVec targetVec v0))
  unless dur?.any (play ≥ ·) do
    infLoop st conv spec startVec targetVec v0 dur? t0

/-- Animate `initial → target` with `spec` (an `infiniteRepeatable`, by
design) for as long as this call is composed; leaving the composition
cancels the loop and releases its frame-clock subscription. Restarts when
`initial` or `target` changes. Mirrors `InfiniteTransition.animateValue`. -/
def animateValue [BEq α] (_ : InfiniteTransition) (conv : VectorConverter α)
    (initial target : α) (spec : AnimationSpec α) : Composable (State α) := do
  have : Nonempty α := ⟨initial⟩
  let st ← remember (mutableStateOf initial)
  LaunchedEffect (initial, target) do
    let startVec := conv.toVector initial
    let targetVec := conv.toVector target
    let v0 := AnimationVector.zero startVec.dim
    let dur? := spec.durationNs conv startVec targetVec v0
    let t0 ← UiTask.awaitFrame
    infLoop st conv spec startVec targetVec v0 dur? t0
  return st.asState

/-- `Float32` infinite property. Mirrors `InfiniteTransition.animateFloat`. -/
def animateFloat (it : InfiniteTransition) (initial target : Float32)
    (spec : AnimationSpec Float32) : Composable (State Float32) :=
  it.animateValue .float32 initial target spec

end InfiniteTransition

end Compose
