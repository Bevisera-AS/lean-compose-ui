module

public import Compose.Ui.Input.Pointer
public meta import Compose.Ui.Input.Pointer

public section

namespace Compose

/-!
# Gesture detectors (`Compose/Foundation/Gestures.lean`)

Coroutine gesture detectors over `PointerInputScope`, mirroring
`androidx.compose.foundation.gestures`. Each takes the scope as its *last*
parameter so partial application reads like Compose:
`Modifier.pointerInput 0 (detectTapGestures (onTap := some fun _ => onClick))`.

Documented deviations from Compose (single-pointer desktop model):
* **Double tap** uses SDL's consecutive-click counter (an even `clicks` on
  the press) instead of a timeout window — so `onTap` still fires for the
  first click of a double-click; there is no first-tap delay.
* **Drag cancel** means the pointer left the window mid-drag (the router
  synthesizes `exit` into a captured path); Compose's
  consumed-by-someone-else cancellation cannot occur here because consumed
  events are never delivered.
* Positions are local to the `pointerInput` element's region; a release
  outside `[0, size)` is a click-cancel.
-/

/-- How a press ended. -/
inductive PressOutcome where
  /-- The button was released (consumed); position may be out of bounds. -/
  | released (ev : PointerEvent)
  /-- The pointer left the window while pressed. -/
  | cancelled
  /-- The long-press timeout fired first. -/
  | longPressed
  deriving Inhabited

/-- Await events until the press of `button` ends: its `release` (consumed)
or an `exit`. Intermediate moves/presses — and releases of *other* buttons
(a chorded right click during a held left press) — pass through unconsumed. -/
private partial def awaitReleaseOrCancel (button : Option Sdl.MouseButton)
    (scope : PointerInputScope) : UiTask PressOutcome := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .release =>
    if ev.button == button then ev.consume; return .released ev
    else awaitReleaseOrCancel button scope
  | .exit => return .cancelled
  | _ => awaitReleaseOrCancel button scope

/-- The receiver of `detectTapGestures`' `onPress`: where the press went down
and a way to suspend until it ends. Mirrors
`androidx.compose.foundation.gestures.PressGestureScope`. -/
structure PressScope where
  /-- The element's pointer scope. -/
  scope : PointerInputScope
  /-- Press position, element-local px. -/
  pressPosition : Offset
  /-- The button that went down (a finger's contact is modeled as `.left`);
  only its release ends the press — chorded other-button releases don't. -/
  pressButton : Option Sdl.MouseButton
  /-- The press outcome, memoized so `onPress` and the detector share one
  event consumer (the queue has a single waiter slot). -/
  outcomeRef : IO.Ref (Option PressOutcome)
  /-- Long-press timeout to race against the *first* await (`none` = no
  long-press handler installed). -/
  longPressMs : Option UInt32
  /-- Whether the long-press race is still to be armed. -/
  armRef : IO.Ref Bool

namespace PressScope

/-- Suspend until the press ends and memoize the outcome; the first await
races the long-press timeout when one is armed. -/
private def awaitOutcome (ps : PressScope) : UiTask PressOutcome := do
  match ← ps.outcomeRef.get with
  | some o => return o
  | none =>
    let arm ← ps.armRef.modifyGet fun a => (a, false)
    let o ← match ps.longPressMs with
      | some ms =>
        if arm then
          UiTask.race
            (do UiTask.delay ms; pure .longPressed)
            (awaitReleaseOrCancel ps.pressButton ps.scope)
        else
          awaitReleaseOrCancel ps.pressButton ps.scope
      | none => awaitReleaseOrCancel ps.pressButton ps.scope
    ps.outcomeRef.set (some o)
    return o

/-- Suspend until the press ends; `true` iff it was released inside the
element's bounds (a completed click). `false` on release-outside, window
leave, or a long-press win. Mirrors `PressGestureScope.tryAwaitRelease`. -/
def tryAwaitRelease (ps : PressScope) : UiTask Bool := do
  match ← ps.awaitOutcome with
  | .released ev => ps.scope.containsLocal ev.position
  | _ => return false

end PressScope

/-- Detect taps, double taps (SDL `clicks`, see the module docstring), long
presses (fires after `longPressMillis` without a release and suppresses the
tap), secondary (right-button) taps, and raw presses (`onPress` runs per
primary press and may `tryAwaitRelease`). Presses and releases are consumed.

`onSecondaryTap` fires on a completed right-button click (release inside the
element) — the desktop context-menu gesture, mirroring Compose desktop's
`Modifier.onClick(matcher = PointerMatcher.mouse(PointerButton.Secondary))`.
When it is omitted, right-button presses flow through the primary handlers
(the pre-M14b behavior). Mirrors
`androidx.compose.foundation.gestures.detectTapGestures`. -/
partial def detectTapGestures
    (onTap : Option (Offset → IO Unit) := none)
    (onDoubleTap : Option (Offset → IO Unit) := none)
    (onLongPress : Option (Offset → IO Unit) := none)
    (onSecondaryTap : Option (Offset → IO Unit) := none)
    (onPress : Option (PressScope → UiTask Unit) := none)
    (longPressMillis : UInt32 := 500)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    if ev.button == some .right && onSecondaryTap.isSome then
      -- Secondary click: fire on a release inside the element (no double/long
      -- press variants — the desktop context-menu gesture is a plain click).
      if let .released rel ← awaitReleaseOrCancel ev.button scope then
        if ← scope.containsLocal rel.position then
          if let some st := onSecondaryTap then st rel.position
    else
      let ps : PressScope :=
        { scope, pressPosition := ev.position, pressButton := ev.button
          outcomeRef := ← IO.mkRef none
          longPressMs := if onLongPress.isSome then some longPressMillis else none
          armRef := ← IO.mkRef true }
      if let some press := onPress then press ps
      match ← ps.awaitOutcome with
      | .longPressed =>
        if let some lp := onLongPress then lp ev.position
      | .released rel =>
        if ← scope.containsLocal rel.position then
          if rel.clicks ≥ 2 && rel.clicks % 2 == 0 && onDoubleTap.isSome then
            if let some dt := onDoubleTap then dt rel.position
          else if let some tap := onTap then tap rel.position
      | .cancelled => pure ()
  detectTapGestures onTap onDoubleTap onLongPress onSecondaryTap onPress
    longPressMillis scope

/-- Detect drags: after a press moves beyond `touchSlop` px, `onDragStart`
fires (then `onDrag position delta` per move, moves consumed), ending with
`onDragEnd` on release or `onDragCancel` when the pointer leaves the window.
A press released within the slop is not a drag (nothing fires). Mirrors
`androidx.compose.foundation.gestures.detectDragGestures`. -/
partial def detectDragGestures
    (onDrag : Offset → Offset → IO Unit)
    (onDragStart : Offset → IO Unit := fun _ => pure ())
    (onDragEnd : IO Unit := pure ())
    (onDragCancel : IO Unit := pure ())
    (touchSlop : Float32 := 4)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    track ev.button ev.position false ev.position
  detectDragGestures onDrag onDragStart onDragEnd onDragCancel touchSlop scope
where
  /-- Follow one press of `button`: `started` once past the slop, `last` =
  previous drag position (deltas accumulate from the press position). A
  chorded other button's release passes through without ending the drag. -/
  track (button : Option Sdl.MouseButton) (pressPos : Offset) (started : Bool)
      (last : Offset) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      if started then
        ev.consume
        onDrag ev.position (ev.position - last)
        track button pressPos started ev.position
      else if pressPos.distance ev.position > touchSlop then
        ev.consume
        onDragStart ev.position
        onDrag ev.position (ev.position - pressPos)
        track button pressPos true ev.position
      else
        track button pressPos started last
    | .release =>
      if ev.button == button then
        if started then
          ev.consume
          onDragEnd
      else
        track button pressPos started last
    | .exit =>
      if started then onDragCancel
    | _ => track button pressPos started last

/-- Stream hover enter/move/exit callbacks (the raw-element diet version of
hover-interaction plumbing; see `Modifier.hoverable` for the
`InteractionSource` form). Mirrors a `awaitPointerEvent` enter/exit loop in
Compose samples. -/
partial def detectHover
    (onEnter : Offset → IO Unit := fun _ => pure ())
    (onExit : IO Unit := pure ())
    (onMove : Offset → IO Unit := fun _ => pure ())
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .enter => onEnter ev.position
  | .exit => onExit
  | .move => onMove ev.position
  | _ => pure ()
  detectHover onEnter onExit onMove scope

end Compose

end
