import Sdl.Mouse
import Sdl.Keycode
import Compose.Core.Geometry
import Compose.Core.Density
import Compose.Runtime.Scheduler

namespace Compose

/-!
# Pointer events (`Compose/Ui/Input/Pointer.lean`)

The pointer half of M6's input story, below the modifier chain: the
`PointerEvent` record SDL mouse events translate into, and the per-element
runtime machinery behind `Modifier.pointerInput` — an event queue plus a
parked-continuation slot that `PointerInputScope.awaitEvent` suspends on and
dispatch resumes *synchronously* (so a handler's `consume` is observed within
the same dispatch, mirroring Compose's main-pass delivery).

Consumption is DESIGN.md's simplified model: one main pass with a mutable
per-dispatch `consumed` flag (`PointerEvent.consume`/`isConsumed` close over
it); tunnel/tunnel-final passes are not modeled. Hit testing and dispatch
over the `LayoutNode` tree live in `Compose.Ui.Input.HitTest` (this module
must stay below `Modifier`, which carries the handlers).
-/

/-- What a pointer did. `enter`/`exit` are produced by hover-path diffing
(and window leave), the rest translate SDL mouse events directly. Mirrors
`androidx.compose.ui.input.pointer.PointerEventType`. -/
inductive PointerEventType where
  | press
  | release
  | move
  | scroll
  | enter
  | exit
  deriving Repr, BEq, Inhabited

/-- One pointer event as delivered to handlers. `position` is in the
receiving `pointerInput` region's local coordinates (render pixels; root
coordinates before dispatch localizes it). `consume`/`isConsumed` close over
the per-dispatch consumed flag — consuming stops delivery to outer handlers
(leaf→root bubbling). Mirrors `androidx.compose.ui.input.pointer.PointerEvent`
+ `PointerInputChange.consume()`, collapsed to the single-pointer desktop
case. -/
structure PointerEvent where
  eventType : PointerEventType
  position : Offset
  /-- The button that changed on `press`/`release` (`none` otherwise). -/
  button : Option Sdl.MouseButton := none
  /-- Buttons held down *after* the event (tracked by the input manager). -/
  buttons : Sdl.MouseButtonFlags := .none
  /-- SDL's consecutive-click counter on `press`/`release` (double-click = 2). -/
  clicks : UInt8 := 0
  /-- Wheel delta in SDL wheel ticks (`scroll` only), in *content* terms with
  the OS scroll-direction preference already applied. SDL's axes point
  opposite ways: positive `y` scrolls toward the content start (up), positive
  `x` toward the content end (right). -/
  scrollDelta : Offset := .zero
  /-- Keyboard modifiers held at event time. -/
  mods : Sdl.Keymod := .none
  /-- SDL timestamp, nanoseconds. -/
  timestamp : UInt64 := 0
  /-- Mark the event consumed for this dispatch. -/
  consume : IO Unit := pure ()
  /-- Whether some handler already consumed this dispatch. -/
  isConsumed : IO Bool := pure false
  /-- Ask the router to hand the rest of the gesture to the receiving
  element: captured-path targets *inner* to it get a synthetic `exit` (the
  gesture-cancel a window leave delivers — a pending press under the finger
  cancels instead of clicking) and stop receiving the capture's events.
  Rebound per element during captured `move` dispatch; a no-op elsewhere.
  The router half of a drag-scroll taking over past the touch slop. -/
  steal : IO Unit := pure ()

instance : Inhabited PointerEvent := ⟨{ eventType := .press, position := .zero }⟩

/-- Cap on buffered events per `pointerInput` element (a handler that never
awaits should not grow memory; oldest events drop first). -/
def PointerInput.queueCap : Nat := 64

/-- Runtime state of one `Modifier.pointerInput` element on a `LayoutNode`:
its relaunch key, current chain index (updated on reconcile), the buffered
events, the parked `awaitEvent` continuation, and the handler coroutine's
job. Created/cancelled by the reconcile pass (see
`LayoutNode.reconcilePointerInputs`). Mirrors the suspending pointer-input
node of `Modifier.pointerInput`. -/
structure PointerInputState where
  /-- Relaunch key: the coroutine restarts when it changes. -/
  key : UInt64
  /-- Index of the element in the node's modifier chain (kept current by
  reconcile so dispatch and `size` resolve the right wrapper region). -/
  elemIdx : IO.Ref Nat
  /-- Events delivered while no `awaitEvent` was parked (bounded). -/
  queue : IO.Ref (Array PointerEvent)
  /-- The parked `awaitEvent` continuation with its coroutine's cancel token
  (a cancelled waiter is discarded without consuming the event). -/
  waiter : IO.Ref (Option (CancelToken × (PointerEvent → IO Unit)))
  /-- The most recently delivered event. -/
  lastEvent : IO.Ref (Option PointerEvent)
  /-- The handler coroutine, cancelled on key change / node removal. -/
  job : IO.Ref (Option Job)

namespace PointerInputState

/-- Fresh state (no job yet). -/
def create (key : UInt64) (elemIdx : Nat) : IO PointerInputState :=
  return { key
           elemIdx := ← IO.mkRef elemIdx
           queue := ← IO.mkRef #[]
           waiter := ← IO.mkRef none
           lastEvent := ← IO.mkRef none
           job := ← IO.mkRef none }

/-- Deliver one event: resume the parked `awaitEvent` continuation
*synchronously* (so consumption during this dispatch is observed) or buffer
the event (bounded by `PointerInput.queueCap`). A waiter whose coroutine was
cancelled is dropped without eating the event — a raced-out awaiter (e.g. a
long-press timer won) must not swallow the release. -/
def offer (st : PointerInputState) (ev : PointerEvent) : IO Unit := do
  st.lastEvent.set (some ev)
  match ← st.waiter.modifyGet fun w => (w, none) with
  | some (tok, k) =>
    if ← tok.isCancelled then
      buffer st ev
    else
      k ev
  | none => buffer st ev
where
  /-- Push onto the bounded queue, dropping the oldest event when full. -/
  buffer (st : PointerInputState) (ev : PointerEvent) : IO Unit :=
    st.queue.modify fun q =>
      (if q.size ≥ PointerInput.queueCap then q.eraseIdx! 0 else q).push ev

/-- Cancel the handler coroutine (node removal / key change). -/
def cancel (st : PointerInputState) : IO Unit := do
  if let some j ← st.job.get then j.cancel

end PointerInputState

/-- The receiver of a `Modifier.pointerInput` handler: await pointer events
delivered to this element, query the decorated wrapper's size, peek the last
event. Mirrors `androidx.compose.ui.input.pointer.PointerInputScope`
(collapsed: `awaitPointerEventScope` is implicit — the handler awaits
directly). -/
structure PointerInputScope where
  /-- The element's runtime state (queue/waiter). -/
  state : PointerInputState
  /-- Size of the wrapper the element decorates (its hit region), in px.
  Mirrors `PointerInputScope.size`. -/
  getSize : IO IntSize
  /-- The node's density (px-per-dp conversions — touch slop). Mirrors
  `PointerInputScope : Density`. -/
  getDensity : IO Density := pure {}

namespace PointerInputScope

/-- Suspend until the next pointer event delivered to this element (buffered
events resume immediately, in order). Mirrors
`AwaitPointerEventScope.awaitPointerEvent` (main pass only). -/
def awaitEvent (s : PointerInputScope) : UiTask PointerEvent :=
  ⟨fun _ tok k => do
    unless ← tok.isCancelled do
      let q ← s.state.queue.get
      if h : 0 < q.size then
        s.state.queue.set (q.eraseIdx 0)
        k q[0]
      else
        s.state.waiter.set (some (tok, k))⟩

/-- Size of the wrapper this element decorates, in px. -/
def size (s : PointerInputScope) : IO IntSize := s.getSize

/-- The node's density, for dp→px conversions in gesture math. -/
def density (s : PointerInputScope) : IO Density := s.getDensity

/-- The most recently delivered event (`none` before the first). Mirrors
`AwaitPointerEventScope.currentEvent`. -/
def currentEvent (s : PointerInputScope) : IO (Option PointerEvent) :=
  s.state.lastEvent.get

/-- Whether `p` (element-local px) is inside the element's region. -/
def containsLocal (s : PointerInputScope) (p : Offset) : IO Bool := do
  let sz ← s.getSize
  return 0 ≤ p.x && p.x < sz.width.toFloat32 && 0 ≤ p.y && p.y < sz.height.toFloat32

end PointerInputScope

end Compose
