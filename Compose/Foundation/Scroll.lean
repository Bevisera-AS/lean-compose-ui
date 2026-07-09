import Compose.Ui.Modifier
import Compose.Runtime.Composer
import Compose.Runtime.Macro
import Compose.Animation.Spec

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
-/

/-- Pixels scrolled per mouse-wheel notch (the desktop-Compose-ish line
step). -/
def wheelScrollStep : Float32 := 50

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

instance : Nonempty ScrollState :=
  ⟨{ id := 0
     valueState := Classical.choice inferInstance
     maxValueState := Classical.choice inferInstance
     viewportSizeState := Classical.choice inferInstance
     contentSizeState := Classical.choice inferInstance }⟩

namespace ScrollState

/-- Fresh state at offset `initial`. -/
def create (initial : Float32 := 0) : IO ScrollState :=
  return { id := (← freshId).toUInt64
           valueState := ← mutableStateOf (max 0 initial)
           maxValueState := ← mutableStateOf 0
           viewportSizeState := ← mutableStateOf 0
           contentSizeState := ← mutableStateOf 0 }

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
frame clock. A concurrent user scroll is not cancelled — both write and the
last one wins (documented simplification of Compose's `MutatorMutex`).
Mirrors `ScrollState.animateScrollTo`. -/
partial def animateScrollTo (s : ScrollState) (target : Float32)
    (spec : AnimationSpec Float32 := .tween 300 0 .fastOutSlowIn) : UiTask Unit := do
  let conv := VectorConverter.float32
  let startVec := conv.toVector (← s.valueState.cell.get)
  let targetVec := conv.toVector target
  let v0 := AnimationVector.zero startVec.dim
  let dur? := spec.durationNs conv startVec targetVec v0
  let t0 ← UiTask.awaitFrame
  loop conv startVec targetVec v0 dur? t0
where
  loop (conv : VectorConverter Float32) (startVec targetVec v0 : AnimationVector)
      (dur? : Option UInt64) (t0 : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    let play := if ns ≤ t0 then 0 else ns - t0
    if dur?.any (play ≥ ·) then
      s.scrollTo target
    else
      s.scrollTo (conv.fromVector (spec.valueAt conv play startVec targetVec v0))
      loop conv startVec targetVec v0 dur? t0

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
  -- Positive wheel y = away from the user = toward the content start.
  let notches := if vertical then delta.y else delta.x
  if notches == 0 then return .zero
  let moved ← state.scrollBy (-notches * wheelScrollStep)
  if moved == 0 then return .zero
  return if vertical then ⟨0, notches⟩ else ⟨notches, 0⟩

namespace Modifier

/-- Make the content scrollable vertically: content measures with unbounded
height, the container reports `min(content, incoming max)`, clips to its
bounds, offsets the content by `-state.value`, and consumes wheel events when
it can scroll in their direction. Mirrors
`androidx.compose.foundation.verticalScroll(state)`. -/
def verticalScroll (state : ScrollState) (m : Modifier := {}) : Modifier :=
  m.onScroll (scrollWheelHandler state true)
  |>.clip .rectangle
  |>.customLayout (mixKeys (stringKey "Compose.Modifier.verticalScroll") state.id)
      (scrollLayoutBlock state true)

/-- Horizontal counterpart of `verticalScroll`. Mirrors
`androidx.compose.foundation.horizontalScroll(state)`. -/
def horizontalScroll (state : ScrollState) (m : Modifier := {}) : Modifier :=
  m.onScroll (scrollWheelHandler state false)
  |>.clip .rectangle
  |>.customLayout (mixKeys (stringKey "Compose.Modifier.horizontalScroll") state.id)
      (scrollLayoutBlock state false)

end Modifier

end Compose
