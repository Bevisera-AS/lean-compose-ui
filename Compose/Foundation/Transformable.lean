module

public import Compose.Ui.Modifier
public meta import Compose.Ui.Modifier
public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer
public import Compose.Runtime.Effects
public meta import Compose.Runtime.Effects
public import Std.Data.HashMap.Basic
public meta import Std.Data.HashMap.Basic

public section

namespace Compose

/-!
# Transform gestures (`Compose/Foundation/Transformable.lean`)

Multi-pointer transform (pinch) gestures: `detectTransformGestures` derives
zoom, pan (centroid displacement), and rotation from two or more concurrent
pointers' streams — the router already delivers every captured pointer's
events to the node's `pointerInput` queue, each tagged with its
`PointerEvent.pointerId`, so no extra plumbing is needed and the whole
gesture is drivable headlessly. `Modifier.transformable` +
`rememberTransformableState` wrap it in the state-object shape. Mirrors
`androidx.compose.foundation.gestures.detectTransformGestures` /
`Modifier.transformable`.

Interplay with drag-scroll: the detector runs in the *final pass* on the
transformable node (like drag-scroll it must observe gestures whose presses
inner clickables consumed), and the final sweep is leaf→root, so it sees
each move before an enclosing scrollable's observer. Below the transform slop it
consumes nothing (a single-finger drag on the node still scrolls the parent);
once the cumulative zoom+pan+rotation motion crosses the slop it steals the
gesture (`PointerEvent.steal` — pending clicks under either finger cancel)
and consumes every further move, so the scrollable's session goes dead:
pinch-on-scrollable zooms, it does not scroll.

The math is pure and `#guard`-tested (`TransformDelta.compute`,
`transformCentroid`, `transformMotion`); angles are degrees, positive =
clockwise in screen coordinates (y down).
-/

/-- Touch slop for transform gestures, dp: cumulative zoom/pan/rotation
motion below this leaves the pointers to whoever else wants them (a click, a
parent's drag-scroll). Matches `dragScrollSlop`. -/
def transformTouchSlop : Dp := 8

/-- Centroid (mean) of the pointer positions; `.zero` when empty. Mirrors
`calculateCentroid`. -/
def transformCentroid (ps : Array Offset) : Offset :=
  if ps.size = 0 then .zero
  else (ps.foldl (· + ·) Offset.zero) * (1.0 / ps.size.toFloat.toFloat32)

/-- Mean distance of the pointers from their centroid — the gesture's radius
(`0` for fewer than two pointers). Mirrors `calculateCentroidSize`. -/
def transformSpan (ps : Array Offset) : Float32 :=
  if ps.size < 2 then 0
  else
    let c := transformCentroid ps
    (ps.foldl (fun acc p => acc + p.distance c) 0) / ps.size.toFloat.toFloat32

/-- One frame of a multi-pointer transform, from previous → current positions
(arrays index-aligned; pointers past the shorter array are ignored). -/
structure TransformDelta where
  /-- Centroid displacement, px. -/
  pan : Offset := .zero
  /-- Ratio of mean centroid distances (`1` with fewer than two pointers or a
  degenerate previous frame). -/
  zoom : Float32 := 1
  /-- Mean signed angle change, degrees in `[-180, 180)`, positive =
  clockwise (screen coordinates, y down); `0` with fewer than two pointers. -/
  rotation : Float32 := 0
  deriving Repr, Inhabited

/-- Wrap an angle into `[-180, 180)` (the atan2 branch cut crossing must not
read as a full turn). -/
private def wrapDegrees (a : Float) : Float :=
  a - 360 * ((a + 180) / 360).floor

/-- Angle of `v` around `.zero`, degrees. -/
private def angleDeg (v : Offset) : Float :=
  Float.atan2 v.y.toFloat v.x.toFloat * 180 / 3.141592653589793

/-- Compute the transform one event step produced: centroids give `pan`,
mean centroid-distance ratio gives `zoom`, the mean per-pointer angle change
around the centroid gives `rotation` (pointers sitting on the centroid are
skipped — they carry no angle). Mirrors `calculateZoom`/`calculatePan`/
`calculateRotation`, unweighted. -/
def TransformDelta.compute (prev cur : Array Offset) : TransformDelta := Id.run do
  let n := min prev.size cur.size
  if n == 0 then return {}
  let prev := prev.extract 0 n
  let cur := cur.extract 0 n
  let c0 := transformCentroid prev
  let c1 := transformCentroid cur
  let pan := c1 - c0
  if n < 2 then return { pan }
  let d0 := transformSpan prev
  let d1 := transformSpan cur
  let zoom := if d0 > 1e-6 then d1 / d0 else 1
  let mut rotSum : Float := 0
  let mut rotN : Nat := 0
  for i in [0:n] do
    let v0 := prev[i]! - c0
    let v1 := cur[i]! - c1
    if v0.distance .zero > 1e-6 && v1.distance .zero > 1e-6 then
      rotSum := rotSum + wrapDegrees (angleDeg v1 - angleDeg v0)
      rotN := rotN + 1
  let rotation := if rotN == 0 then 0 else (rotSum / rotN.toFloat).toFloat32
  return { pan, zoom, rotation }

/-- Arc length a cumulative `rotation` (degrees) swept at radius `span`, px —
rotation's contribution to the touch-slop race. -/
def rotationMotion (rotation span : Float32) : Float32 :=
  rotation.abs * 3.14159265 / 180 * span

/-- Cumulative gesture motion for the transform touch slop: the largest of
the zoom motion (`|1 − zoom| · span`), the pan distance, and the rotation arc
length. Mirrors the slop accumulation in `detectTransformGestures`. -/
def transformMotion (zoom rotation : Float32) (pan : Offset) (span : Float32) :
    Float32 :=
  max (max ((1 - zoom).abs * span) (pan.distance .zero))
    (rotationMotion rotation span)

-- Centroid / span.
#guard transformCentroid #[] == .zero
#guard transformCentroid #[⟨2, 4⟩] == ⟨2, 4⟩
#guard transformCentroid #[⟨0, 0⟩, ⟨10, 20⟩] == ⟨5, 10⟩
#guard transformSpan #[⟨0, 0⟩, ⟨6, 8⟩] == 5
-- Pure zoom: two points diverge symmetrically → zoom 2, no pan, no rotation.
#guard let d := TransformDelta.compute #[⟨0, 0⟩, ⟨2, 0⟩] #[⟨-1, 0⟩, ⟨3, 0⟩]
       d.zoom == 2 && d.pan == .zero && d.rotation == 0
-- Pure pan: both points +⟨10, 5⟩ → pan carries, zoom 1, no rotation.
#guard let d := TransformDelta.compute #[⟨0, 0⟩, ⟨4, 0⟩] #[⟨10, 5⟩, ⟨14, 5⟩]
       d.pan == ⟨10, 5⟩ && d.zoom == 1 && d.rotation == 0
-- Pure rotation: a 90° orbit (y down: (1,0)→(0,1) is clockwise) → +90°.
#guard let d := TransformDelta.compute #[⟨1, 0⟩, ⟨-1, 0⟩] #[⟨0, 1⟩, ⟨0, -1⟩]
       (d.rotation - 90).abs < 0.001 && d.zoom == 1 && d.pan == .zero
-- Degenerate: both pointers on one spot → identity.
#guard let d := TransformDelta.compute #[⟨5, 5⟩, ⟨5, 5⟩] #[⟨5, 5⟩, ⟨5, 5⟩]
       d.zoom == 1 && d.rotation == 0 && d.pan == .zero
-- Angle wrap: a small step across the ±180° cut is small, not a full turn.
#guard let d := TransformDelta.compute #[⟨-1, -0.1⟩, ⟨1, 0.1⟩] #[⟨-1, 0.1⟩, ⟨1, -0.1⟩]
       d.rotation.abs < 15
-- Motion accumulation.
#guard transformMotion 1 0 ⟨3, 4⟩ 100 == 5
#guard transformMotion 2 0 .zero 10 == 10
#guard (transformMotion 1 90 .zero 2 - 3.14159265).abs < 0.001

/-- Detect multi-pointer transform gestures: once the cumulative
zoom+pan+rotation motion of two (or more) concurrent pointers passes the
touch slop, `onGesture centroid pan zoom rotation` fires per move (moves
stolen + consumed — see the module docstring for the scroll interplay).
`panZoomLock`: when pan/zoom win the slop race, rotation stays locked out
for the whole gesture. Positions element-local px; a consumed move below
the slop (an inner drag owns the pointers) stands the detector down until
the gesture ends. Mirrors
`androidx.compose.foundation.gestures.detectTransformGestures`. -/
partial def detectTransformGestures
    (onGesture : Offset → Offset → Float32 → Float32 → IO Unit)
    (panZoomLock : Bool := false)
    (touchSlop : Dp := transformTouchSlop)
    (scope : PointerInputScope) : UiTask Unit :=
  idle {}
where
  /-- Tracked positions, sorted by pointer id (stable index alignment across
  steps — the maps differ by one updated value). -/
  positionsOf (ptrs : Std.HashMap UInt64 Offset) : Array Offset :=
    (ptrs.toArray.qsort (fun a b => a.1 < b.1)).map (·.2)
  /-- Fold a non-move event into the tracked set (primary presses add,
  release/exit removes). -/
  fold (ptrs : Std.HashMap UInt64 Offset) (ev : PointerEvent) :
      Std.HashMap UInt64 Offset :=
    match ev.eventType with
    | .press => if ev.button == some .left then ptrs.insert ev.pointerId ev.position else ptrs
    | .release | .exit => ptrs.erase ev.pointerId
    | _ => ptrs
  /-- Fewer than two pointers down: keep the roster current; a second press
  arms the slop race. A routed trackpad `pinch` step (see the router — only
  delivered while no finger gesture is live) fires directly, scale-only at
  the cursor: SDL's recognizer already applied its own threshold, so there is
  no slop to race. -/
  idle (ptrs : Std.HashMap UInt64 Offset) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      idle (if ptrs.contains ev.pointerId then ptrs.insert ev.pointerId ev.position else ptrs)
    | .pinch =>
      if ptrs.size < 2 then
        ev.consume
        onGesture ev.position .zero ev.zoomDelta 0
      idle ptrs
    | _ =>
      let ptrs := fold ptrs ev
      if ptrs.size ≥ 2 then pending ptrs 1 0 .zero else idle ptrs
  /-- Two+ pointers down, under the slop: accumulate motion; a consumed move
  belongs to an inner gesture (stand down); crossing the slop steals. -/
  pending (ptrs : Std.HashMap UInt64 Offset) (zoomAcc rotAcc : Float32)
      (panAcc : Offset) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      if !ptrs.contains ev.pointerId then pending ptrs zoomAcc rotAcc panAcc
      else if ← ev.isConsumed then dead ptrs
      else
        let ptrs' := ptrs.insert ev.pointerId ev.position
        let d := TransformDelta.compute (positionsOf ptrs) (positionsOf ptrs')
        let zoomAcc := zoomAcc * d.zoom
        let rotAcc := rotAcc + d.rotation
        let panAcc := panAcc + d.pan
        let span := transformSpan (positionsOf ptrs')
        let slop := (← scope.density).dpToPx touchSlop
        if transformMotion zoomAcc rotAcc panAcc span > slop then
          ev.steal
          ev.consume
          -- Rotation joins only if it carried its own weight in the race.
          let useRotation := !(panZoomLock && rotationMotion rotAcc span ≤ slop)
          onGesture (transformCentroid (positionsOf ptrs')) d.pan d.zoom
            (if useRotation then d.rotation else 0)
          active ptrs' useRotation
        else
          pending ptrs' zoomAcc rotAcc panAcc
    | _ =>
      let ptrs := fold ptrs ev
      if ptrs.size < 2 then idle ptrs else pending ptrs zoomAcc rotAcc panAcc
  /-- Past the slop: every tracked move is stolen, consumed, and reported;
  dropping below two pointers ends the gesture. -/
  active (ptrs : Std.HashMap UInt64 Offset) (useRotation : Bool) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      if !ptrs.contains ev.pointerId then active ptrs useRotation
      else
        ev.steal
        ev.consume
        let ptrs' := ptrs.insert ev.pointerId ev.position
        let d := TransformDelta.compute (positionsOf ptrs) (positionsOf ptrs')
        onGesture (transformCentroid (positionsOf ptrs')) d.pan d.zoom
          (if useRotation then d.rotation else 0)
        active ptrs' useRotation
    | _ =>
      let ptrs := fold ptrs ev
      if ptrs.size < 2 then idle ptrs else active ptrs useRotation
  /-- The pointers belong to an inner gesture: sit it out (positions still
  tracked so a later gesture starts fresh). -/
  dead (ptrs : Std.HashMap UInt64 Offset) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      dead (if ptrs.contains ev.pointerId then ptrs.insert ev.pointerId ev.position else ptrs)
    | _ =>
      let ptrs := fold ptrs ev
      if ptrs.size < 2 then idle ptrs else dead ptrs

/-- Receives transform deltas from `Modifier.transformable`. The callback ref
is retargeted every composition (the `rememberUpdatedState` idiom), so
handlers may close over current state. Mirrors `TransformableState`. -/
structure TransformableState where
  /-- Identity for the modifier's `pointerInput` key. -/
  id : UInt64
  /-- `centroid pan zoom rotation` per gesture step (element-local px /
  multiplicative zoom / degrees). -/
  callback : IO.Ref (Offset → Offset → Float32 → Float32 → IO Unit)

instance : Nonempty TransformableState :=
  ⟨{ id := 0, callback := Classical.choice inferInstance }⟩

/-- Remember a `TransformableState` driving `onTransform centroid pan zoom
rotation`; the latest lambda wins on recomposition. Mirrors
`androidx.compose.foundation.gestures.rememberTransformableState`. -/
def rememberTransformableState
    (onTransform : Offset → Offset → Float32 → Float32 → IO Unit) :
    Composable TransformableState := do
  let st : TransformableState ← remember do
    return { id := (← freshId).toUInt64, callback := ← IO.mkRef onTransform }
  SideEffect (st.callback.set onTransform)
  return st

namespace Modifier

/-- Make the element respond to multi-pointer transform gestures (pinch to
zoom/pan/rotate), reporting steps to `state`'s callback. `panZoomLock` locks
rotation out when pan/zoom win the touch-slop race. See
`detectTransformGestures` for the gesture/scroll interplay. Mirrors
`androidx.compose.foundation.gestures.transformable(state)`. -/
def transformable (state : TransformableState) (panZoomLock : Bool := false)
    (m : Modifier := {}) : Modifier :=
  m.pointerInput (mixKeys (stringKey "Compose.Modifier.transformable") state.id)
    (detectTransformGestures
      (fun c pan zoom rot => do (← state.callback.get) c pan zoom rot)
      panZoomLock)
    (pass := .final)

end Modifier

end Compose

end
