module

public import Compose.Ui.Modifier
public meta import Compose.Ui.Modifier
public import Compose.Ui.Input.Velocity
public meta import Compose.Ui.Input.Velocity
public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer
public import Compose.Runtime.Macro
public meta import Compose.Runtime.Macro
public import Compose.Animation.Spec
public meta import Compose.Animation.Spec
public import Compose.Animation.Decay
public meta import Compose.Animation.Decay

public section

namespace Compose

/-!
# Scroll (`Compose/Foundation/Scroll.lean`)

`ScrollState` + `Modifier.verticalScroll`/`horizontalScroll`, mirroring
`androidx.compose.foundation.ScrollState` / `Modifier.verticalScroll`.

The scroll modifier is a `Modifier.customLayout` element: it measures its
content with the scroll axis unbounded (`Constraints.infinity`), reports the
incoming-clamped size as the viewport, clips to bounds, and places the
content offset by `-value`. The offset read happens *inside measurement*, so
a scroll-position write re-lays out exactly the scrolled node (cheap: the
content's cached measurement short-circuits) — the placement-read idiom of
Compose's `ScrollingLayoutNode`. Content/viewport changes re-clamp the value.

Wheel events over the container scroll by `wheelScrollStep` px per notch;
each container consumes only its own axis and only what it could actually
move, so a diagonal wheel event splits between nested horizontal + vertical
containers and end-stopped remainders bubble to outer scrollables.

Pointer drags scroll too (the touch story — SDL synthesizes mouse events
from touch): a *final-pass* `pointerInput` handler per container watches the
gesture even when a clickable child consumed the press, takes it over past
`dragScrollSlop` along its axis (`PointerEvent.steal` cancels the child's
pending press), tracks velocity, and hands off to a `fling` on release —
see `scrollDragHandler`.
-/

/-- Pixels scrolled per mouse-wheel notch (the desktop-Compose-ish line
step). -/
def wheelScrollStep : Float32 := 50

/-- Touch slop for drag-scrolling, dp (Android's `ViewConfiguration`
default): a press that moves less than this along the scroll axis stays a
click; past it the drag owns the gesture. -/
def dragScrollSlop : Dp := 8

/-- Scroll position state for `Modifier.verticalScroll`/`horizontalScroll`:
the offset in px (`0` = start, grows toward the end), plus the observable
extent metrics the last measure produced. Mirrors
`androidx.compose.foundation.ScrollState` (value in `Float32` px rather than
`Int` — smooth wheel/animation steps). -/
structure ScrollState where
  /-- Identity for modifier keys (`customLayout`, wheel handlers). -/
  id : UInt64
  /-- Current scroll offset in px, clamped to `[0, maxValue]` (observable). -/
  valueState : MutableState Float32
  /-- Maximum offset = `max 0 (content − viewport)` (observable; written by
  measurement). Mirrors `ScrollState.maxValue`. -/
  maxValueState : MutableState Float32
  /-- Viewport extent on the scroll axis, px (observable; written by
  measurement). Mirrors `ScrollState.viewportSize`. -/
  viewportSizeState : MutableState Float32
  /-- Content extent on the scroll axis, px (observable; written by
  measurement). -/
  contentSizeState : MutableState Float32
  /-- Mutation generation: bumped by each `animateScrollTo` (and a wheel
  scroll), so a running scroll animation stands down when a newer mutation
  starts — the single-threaded analog of Compose's `MutatorMutex`. -/
  mutationGen : IO.Ref Nat

instance : Nonempty ScrollState :=
  ⟨{ id := 0
     valueState := Classical.choice inferInstance
     maxValueState := Classical.choice inferInstance
     viewportSizeState := Classical.choice inferInstance
     contentSizeState := Classical.choice inferInstance
     mutationGen := Classical.choice inferInstance }⟩

namespace ScrollState

/-- Fresh state at offset `initial`. -/
def create (initial : Float32 := 0) : IO ScrollState :=
  return { id := (← freshId).toUInt64
           valueState := ← MutableState.create (max 0 initial)
           maxValueState := ← MutableState.create 0
           viewportSizeState := ← MutableState.create 0
           contentSizeState := ← MutableState.create 0
           mutationGen := ← IO.mkRef 0 }

/-- Cancel any in-flight scroll animation and claim the mutation lock; returns
the new generation the caller must keep matching to stay live (Compose's
`MutatorMutex.mutate` taking the lock). -/
def interrupt (s : ScrollState) : IO Nat :=
  s.mutationGen.modifyGet fun g => (g + 1, g + 1)

/-- The current offset (observed read). Mirrors `ScrollState.value`. -/
def value (s : ScrollState) : IO Float32 := s.valueState.get

/-- The maximum offset (observed read). Mirrors `ScrollState.maxValue`. -/
def maxValue (s : ScrollState) : IO Float32 := s.maxValueState.get

/-- The viewport extent on the scroll axis (observed read). -/
def viewportSize (s : ScrollState) : IO Float32 := s.viewportSizeState.get

/-- The content extent on the scroll axis (observed read). -/
def contentSize (s : ScrollState) : IO Float32 := s.contentSizeState.get

/-- Jump to `target`, clamped into `[0, maxValue]`. Mirrors
`ScrollState.scrollTo`. -/
def scrollTo (s : ScrollState) (target : Float32) : IO Unit := do
  let maxV ← s.maxValueState.cell.get
  s.valueState.set (min (max target 0) maxV)

/-- Scroll by `delta` px, clamped; returns the amount actually consumed
(`0` when already at the reached end). Mirrors `ScrollState.scrollBy`. -/
def scrollBy (s : ScrollState) (delta : Float32) : IO Float32 := do
  let v ← s.valueState.cell.get
  let maxV ← s.maxValueState.cell.get
  let v' := min (max (v + delta) 0) maxV
  s.valueState.set v'
  return v' - v

/-- Whether the container can scroll toward the end (positive deltas). -/
def canScrollForward (s : ScrollState) : IO Bool :=
  return (← s.valueState.cell.get) < (← s.maxValueState.cell.get)

/-- Whether the container can scroll toward the start (negative deltas). -/
def canScrollBackward (s : ScrollState) : IO Bool :=
  return (← s.valueState.cell.get) > 0

/-- Animate the offset to `target` (clamped at every write), driven by the
frame clock. Starting a new `animateScrollTo` (or a wheel scroll) **interrupts**
any in-flight one via the mutation generation: the superseded loop notices the
stale generation at its next frame and stops without another write, so the last
caller wins cleanly (the single-threaded analog of Compose's `MutatorMutex`).
Mirrors `ScrollState.animateScrollTo`. -/
partial def animateScrollTo (s : ScrollState) (target : Float32)
    (spec : AnimationSpec Float32 := .tween 300 0 .fastOutSlowIn) : UiTask Unit := do
  let myGen ← s.interrupt
  let conv := VectorConverter.float32
  let startVec := conv.toVector (← s.valueState.cell.get)
  let targetVec := conv.toVector target
  let v0 := AnimationVector.zero startVec.dim
  let dur? := spec.durationNs conv startVec targetVec v0
  let t0 ← UiTask.awaitFrame
  loop myGen conv startVec targetVec v0 dur? t0
where
  loop (myGen : Nat) (conv : VectorConverter Float32) (startVec targetVec v0 : AnimationVector)
      (dur? : Option UInt64) (t0 : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    -- A newer mutation took the lock: stand down without touching state.
    if (← s.mutationGen.get) != myGen then return
    let play := if ns ≤ t0 then 0 else ns - t0
    if dur?.any (play ≥ ·) then
      s.scrollTo target
    else
      s.scrollTo (conv.fromVector (spec.valueAt conv play startVec targetVec v0))
      loop myGen conv startVec targetVec v0 dur? t0

/-- Decay-animate the offset from its current position with initial
`velocity` (px/s, positive = toward the end), driven by the frame clock —
the fling a drag-scroll hands off to on release. Interruptible like
`animateScrollTo` (any newer mutation stands it down at its next frame);
stops early on reaching either end of the range. Mirrors the fling half of
`ScrollableState` + `DefaultFlingBehavior`. -/
partial def fling (s : ScrollState) (velocity : Float32)
    (decay : ExponentialDecay := {}) : UiTask Unit := do
  if velocity.abs ≤ decay.absVelocityThreshold then return
  let myGen ← s.interrupt
  let x0 ← s.valueState.cell.get
  let t0 ← UiTask.awaitFrame
  loop myGen x0 t0 (decay.durationNs velocity)
where
  loop (myGen : Nat) (x0 : Float32) (t0 dur : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    if (← s.mutationGen.get) != myGen then return
    let t := if ns ≤ t0 then 0 else ns - t0
    let target :=
      if t ≥ dur then decay.targetValue x0 velocity
      else decay.valueAt x0 velocity t
    s.scrollTo target
    -- Done, or ran into an end of the range (`scrollTo` clamped the rest).
    unless t ≥ dur || target < 0 || target > (← s.maxValueState.cell.get) do
      loop myGen x0 t0 dur

end ScrollState

/-- Remember a `ScrollState` at this composition position. Mirrors
`androidx.compose.foundation.rememberScrollState`. -/
def rememberScrollState (initial : Float32 := 0) : Composable ScrollState :=
  remember (ScrollState.create initial)

/-- The scroll measure block shared by both axes: content measured with the
scroll axis unbounded, viewport = the content size clamped into the incoming
constraints, metrics published, value re-clamped, content placed at
`-value` on the axis. -/
private def scrollLayoutBlock (state : ScrollState) (vertical : Bool) : CustomLayout :=
  ⟨fun _ c measureInner => do
    let innerC :=
      if vertical then { c with minHeight := 0, maxHeight := Constraints.infinity }
      else { c with minWidth := 0, maxWidth := Constraints.infinity }
    let inner ← measureInner innerC
    let size := c.constrain inner
    let (viewport, content) :=
      if vertical then (size.height, inner.height) else (size.width, inner.width)
    state.viewportSizeState.set viewport.toFloat32
    state.contentSizeState.set content.toFloat32
    let maxV := max 0 (content - viewport).toFloat32
    state.maxValueState.set maxV
    -- The observed read: a scroll write re-measures exactly this node.
    let v ← state.valueState.get
    let v' := min (max v 0) maxV
    if v' != v then
      -- Content/viewport change re-clamps (settles next pass, values equal).
      state.valueState.set v'
    let off := -(roundHalfUp v')
    return (size, if vertical then ⟨0, off⟩ else ⟨off, 0⟩)⟩

/-- The wheel handler shared by both axes: scroll by `wheelScrollStep` px per
notch and consume this axis's delta iff movement actually happened — the
cross axis is untouched (a diagonal wheel event feeds the other axis's
container), while an *end-stopped* scrollable consumes nothing and lets its
axis bubble to an outer one (partial movement at the boundary still consumes
the axis in full, the documented pre-M14b behavior). -/
private def scrollWheelHandler (state : ScrollState) (vertical : Bool) :
    Offset → IO Offset := fun delta => do
  -- SDL's axes point opposite ways: positive wheel y = away from the user =
  -- toward the content START (value decreases), but positive wheel x = to
  -- the right = toward the content END (value increases) — so only y flips.
  let notches := if vertical then delta.y else delta.x
  if notches == 0 then return .zero
  -- A user wheel is a mutation too: cancel any running scroll animation.
  let _ ← state.interrupt
  let moved ← state.scrollBy ((if vertical then -notches else notches) * wheelScrollStep)
  if moved == 0 then return .zero
  return if vertical then ⟨0, notches⟩ else ⟨notches, 0⟩

/-- The drag-to-scroll handler shared by both axes, installed as a
**final-pass** `pointerInput` (it must observe the presses and releases that
inner clickables consume — see `PointerPass.final`). Per gesture: a primary
press stops any running fling (the catch) and arms tracking; once the
pointer moves `dragScrollSlop` px (density-scaled) along the axis, the
handler *steals* the gesture (`PointerEvent.steal` — the router cancels the
pressed child's pending click) and feeds further moves into
`ScrollState.scrollBy` (consumed, so outer containers stand off); release
hands the tracked velocity to `ScrollState.fling` on its own coroutine. A
gesture that exceeds the slop *across* the axis first, or one an inner drag
(a slider) consumes, is left alone. Mirrors the drag half of
`Modifier.scrollable`'s touch handling. -/
private partial def scrollDragHandler (state : ScrollState) (vertical : Bool)
    (scope : PointerInputScope) : UiTask Unit :=
  idle
where
  axisOf (p : Offset) : Float32 := if vertical then p.y else p.x
  crossOf (p : Offset) : Float32 := if vertical then p.x else p.y
  /-- No gesture in flight: a primary press catches a running fling and arms
  tracking (even when a child consumed it — gesture boundaries stay visible
  to a final-pass observer). -/
  idle : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.eventType == .press && ev.button == some .left then
      let _ ← state.interrupt
      track ev.position (VelocityTracker.empty.add ev.timestamp (axisOf ev.position))
    else
      idle
  /-- Pressed, still within the slop: decide between click (release first),
  our drag (axis slop first), someone else's gesture (cross slop first or a
  consumed move), and cancel (window leave). -/
  track (origin : Offset) (vt : VelocityTracker) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      if ← ev.isConsumed then
        -- An inner drag (a slider) owns this gesture.
        dead
      else
        let vt := vt.add ev.timestamp (axisOf ev.position)
        let slop := (← scope.density).dpToPx dragScrollSlop
        let d := axisOf ev.position - axisOf origin
        if d.abs > slop then
          ev.steal
          ev.consume
          let _ ← state.interrupt
          -- Start from the slop edge, not with a jump over the dead zone.
          let _ ← state.scrollBy (-(d - (if d > 0 then slop else -slop)))
          drag (axisOf ev.position) vt
        else if (crossOf ev.position - crossOf origin).abs > slop then
          dead
        else
          track origin vt
    | .release => if ev.button == some .left then idle else track origin vt
    | .exit => idle
    | _ => track origin vt
  /-- Past the slop, gesture stolen: moves scroll (consumed), release flings,
  window leave cancels without a fling. -/
  drag (lastAxis : Float32) (vt : VelocityTracker) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      ev.consume
      let a := axisOf ev.position
      let _ ← state.scrollBy (-(a - lastAxis))
      drag a (vt.add ev.timestamp a)
    | .release =>
      if ev.button == some .left then
        ev.consume
        -- Content moves opposite the pointer; carry that into the fling.
        let v := -(vt.velocity ev.timestamp)
        let _ ← UiTask.launch (state.fling v)
        idle
      else
        drag lastAxis vt
    | .exit => idle
    | _ => drag lastAxis vt
  /-- This gesture belongs to someone else: sit it out until it ends. -/
  dead : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .release => if ev.button == some .left then idle else dead
    | .exit => idle
    | _ => dead

namespace Modifier

/-- Make the content scrollable vertically: content measures with unbounded
height, the container reports `min(content, incoming max)`, clips to its
bounds, offsets the content by `-state.value`, consumes wheel events when
it can scroll in their direction, and drag-scrolls with a fling on release
(see `scrollDragHandler`). Mirrors
`androidx.compose.foundation.verticalScroll(state)`. -/
def verticalScroll (state : ScrollState) (m : Modifier := {}) : Modifier :=
  m.onScroll (scrollWheelHandler state true)
  |>.pointerInput (mixKeys (stringKey "Compose.Modifier.dragScroll.v") state.id)
      (scrollDragHandler state true) (pass := .final)
  |>.clip .rectangle
  |>.customLayout (mixKeys (stringKey "Compose.Modifier.verticalScroll") state.id)
      (scrollLayoutBlock state true)

/-- Horizontal counterpart of `verticalScroll`. Mirrors
`androidx.compose.foundation.horizontalScroll(state)`. -/
def horizontalScroll (state : ScrollState) (m : Modifier := {}) : Modifier :=
  m.onScroll (scrollWheelHandler state false)
  |>.pointerInput (mixKeys (stringKey "Compose.Modifier.dragScroll.h") state.id)
      (scrollDragHandler state false) (pass := .final)
  |>.clip .rectangle
  |>.customLayout (mixKeys (stringKey "Compose.Modifier.horizontalScroll") state.id)
      (scrollLayoutBlock state false)

end Modifier

end Compose

end
