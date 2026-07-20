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
public import Compose.Animation.SplineDecay
public meta import Compose.Animation.SplineDecay
public import Compose.Animation.Spring
public meta import Compose.Animation.Spring
public import Compose.Foundation.Overscroll
public meta import Compose.Foundation.Overscroll
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

Wheel events over the container scroll by `wheelScrollStep` (dp, resolved
through the container's density) per notch;
each container consumes only its own axis and only what it could actually
move, so a diagonal wheel event splits between nested horizontal + vertical
containers and end-stopped remainders bubble to outer scrollables.

Pointer drags scroll too (the touch story — SDL synthesizes mouse events
from touch): a *final-pass* `pointerInput` handler per container watches the
gesture even when a clickable child consumed the press, takes it over past
`dragScrollSlop` along its axis (`PointerEvent.steal` cancels the child's
pending press), tracks velocity, and hands off to a `fling` on release —
see `scrollDragHandler`.

Nested drag + fling mirror the wheel: the gesture-owning container publishes
the pointer motion (and, on release, velocity) it could not consume through
the per-dispatch leftover cell (`PointerEvent.setLeftover`); the nearest
outer scrollable — whose final-pass observer runs later in the same
leaf→root sweep — *follows* the remainder on its own axis and republishes
what it leaves, so deeper nests cascade. A consumed gesture that publishes
nothing (a slider) still stands outer containers off entirely.
-/

/-- Dp scrolled per mouse-wheel notch (the desktop-Compose-ish line step),
resolved through the container's density like the drag slop — a notch covers
the same visual distance at every scale (Compose Desktop scales its line
step by density too). -/
def wheelScrollStep : Dp := 50

/-- Touch slop for drag-scrolling, dp (Android's `ViewConfiguration`
default): a press that moves less than this along the scroll axis stays a
click; past it the drag owns the gesture. -/
def dragScrollSlop : Dp := 8

/-- Minimal scroll delta revealing `[leading, trailing]` in a viewport
`[0, viewport]`: `0` when already visible — or when an oversized child
already covers the viewport — else the nearest-edge distance (positive
scrolls forward). Mirrors the relocation math of Compose's
`ContentInViewNode`. -/
def bringIntoViewDelta (leading trailing viewport : Float32) : Float32 :=
  if leading >= 0 && trailing <= viewport then 0
  else if leading < 0 && trailing > viewport then 0
  else if leading.abs < (trailing - viewport).abs then leading
  else trailing - viewport

#guard bringIntoViewDelta 10 40 100 == 0        -- already visible
#guard bringIntoViewDelta 150 170 100 == 70     -- below: bottom to the edge
#guard bringIntoViewDelta (-30) (-10) 100 == -30 -- above: top to the edge
#guard bringIntoViewDelta (-10) 120 100 == 0    -- oversized, covering
#guard bringIntoViewDelta 150 300 100 == 150    -- oversized, below: align top
#guard bringIntoViewDelta 0 100 100 == 0        -- exactly filling

/-- Sub-this remainders (px) are `Float32` rounding dust, not real leftover
motion: at a scroll value of a few thousand px the ulp is ~2.4e-4, so a fully
consumed move's `motion + moved` lands near ±1e-4 instead of exactly 0. Dust
published as leftover latches the overscroll band open (`o ≠ 0` routes every
same-direction move into the band, eating the gesture). Well below any real
pull (a slow edge-drag still moves ≥ 0.1 px/frame). -/
def motionDust : Float32 := 0.01

/-- Pointer motion left over after a scroll consumed `moved` px of `motion`
px of pointer travel — the signs are opposite (content moves against the
pointer), so the remainder is their sum: `0` when fully consumed, all of
`motion` at a hard end-stop. Remainders under `motionDust` collapse to an
exact `0`: at real-device scroll values the sum carries `Float32` rounding
dust for *fully consumed* moves, and a nonzero leftover means "the range ran
out" to every consumer downstream (band growth, nested follow). -/
def unconsumedMotion (motion moved : Float32) : Float32 :=
  let rem := motion + moved
  if rem.abs < motionDust then 0 else rem

#guard unconsumedMotion 10 (-10) == 0    -- fully consumed
#guard unconsumedMotion 10 0 == 10       -- end-stopped
#guard unconsumedMotion (-24) 24 == 0
#guard unconsumedMotion 10 (-4) == 6     -- partial: the range ran out mid-move
-- Float32 rounding dust from a fully consumed move is not leftover motion
-- (regression: dust latched the stretch band open and ate the next drags).
#guard unconsumedMotion 55.108765 (-55.108643) == 0
#guard unconsumedMotion (-55.108765) 55.108643 == 0
-- A real sub-pixel end-stop leftover survives.
#guard unconsumedMotion 0.3 0 == 0.3

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
  /-- The overscroll displacement in px along the axis (observable): `> 0` =
  pulled past the start, `< 0` past the end, `0` inside the range. Its
  meaning depends on the container's `OverscrollMode`: in **bounce** mode it
  is the *visible* rubber-banded displacement, added to the content
  placement on top of `-value` (written by the drag rubber-band and
  `settleOverscroll`); in **stretch** mode it is the *raw* pull distance
  (EdgeEffect's `mDistance · viewport`, clamped to ± a viewport) — the
  placement ignores it and the draw-time warp derives its damped intensity
  via `stretchIntensity` (written by the drag and `settleStretch`). -/
  overscrollState : MutableState Float32
  /-- Density of the container's last measure (written by the scroll layout
  block; `1` before it) — resolves `wheelScrollStep`, whose `onScroll`
  handler has no other density source. Plain ref, not observable. -/
  densityRef : IO.Ref Density

instance : Nonempty ScrollState :=
  ⟨{ id := 0
     valueState := Classical.choice inferInstance
     maxValueState := Classical.choice inferInstance
     viewportSizeState := Classical.choice inferInstance
     contentSizeState := Classical.choice inferInstance
     mutationGen := Classical.choice inferInstance
     overscrollState := Classical.choice inferInstance
     densityRef := Classical.choice inferInstance }⟩

namespace ScrollState

/-- Fresh state at offset `initial`. -/
def create (initial : Float32 := 0) : IO ScrollState :=
  return { id := (← freshId).toUInt64
           valueState := ← MutableState.create (max 0 initial)
           maxValueState := ← MutableState.create 0
           viewportSizeState := ← MutableState.create 0
           contentSizeState := ← MutableState.create 0
           mutationGen := ← IO.mkRef 0
           overscrollState := ← MutableState.create 0
           densityRef := ← IO.mkRef {} }

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

/-- The visible overscroll displacement (observed read) — see
`overscrollState`. -/
def overscroll (s : ScrollState) : IO Float32 := s.overscrollState.get

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

/-- The spring phase of `settleOverscroll` under an already-claimed
mutation generation — `fling`'s edge bounce continues into it without
re-interrupting itself. -/
partial def settleOverscrollFrom (s : ScrollState) (myGen : Nat)
    (v0 : Float32 := 0) : UiTask Unit := do
  let o0 ← s.overscrollState.cell.get
  if o0 == 0 && v0 == 0 then return
  let t0 ← UiTask.awaitFrame
  loop o0 t0
where
  loop (o0 : Float32) (t0 : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    if (← s.mutationGen.get) != myGen then return
    let t := if ns ≤ t0 then 0 else ns - t0
    let (x, v) := Spring.evaluate overscrollDamping overscrollStiffness o0 0 v0
      ((t.toFloat / 1e9).toFloat32)
    if Spring.isAtEquilibrium 0 overscrollVisibilityThreshold x v then
      s.overscrollState.set 0
    else
      s.overscrollState.set x
      loop o0 t0

/-- Spring the visible overscroll back to rest (stiffness 200, critically
damped, 0.5 px settle threshold — CMP's Cupertino constants), carrying an
initial overscroll-space velocity `v0` (px/s — the bounce a fling's or
drag's residual velocity buys as overshoot). Interruptible like `fling`:
any newer mutation stands it down at its next frame. -/
def settleOverscroll (s : ScrollState) (v0 : Float32 := 0) : UiTask Unit := do
  s.settleOverscrollFrom (← s.interrupt) v0

/-- The stretch-mode release/absorb settle under an already-claimed mutation
generation (`fling`'s edge absorb continues into it without re-interrupting
itself): per frame, one `stretchSettleStep` on the band's magnitude (the
sign factors out; `v0` is the overscroll-space velocity, px/s — an absorb
from rest grows the band before the spring pulls it home). Sub-ms frames
merge into the next step (EdgeEffect's `deltaT` guard) and ΔT clamps to
≤ 0.1 s — a backgrounded app's resume gap must not feed the near-critical
closed form a huge step (AOSP is frame-locked and needs no clamp). A press
interrupts via the generation, freezing the band mid-flight (the catch);
the next pull continues from the frozen value. -/
partial def settleStretchFrom (s : ScrollState) (myGen : Nat)
    (v0 : Float32 := 0) : UiTask Unit := do
  let o0 ← s.overscrollState.cell.get
  if o0 == 0 && v0 == 0 then return
  let sign : Float32 :=
    if o0 != 0 then (if o0 < 0 then -1 else 1)
    else (if v0 < 0 then -1 else 1)
  let t0 ← UiTask.awaitFrame
  loop sign o0.abs (v0 * sign) t0
where
  loop (sign x v : Float32) (prev : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    if (← s.mutationGen.get) != myGen then return
    let dtNs := if ns ≤ prev then 0 else ns - prev
    if dtNs < 1000000 then
      loop sign x v prev
    else
      let dt := min ((dtNs.toFloat / 1e9).toFloat32) 0.1
      let (x', v', settled) := stretchSettleStep x v dt
        (← s.viewportSizeState.cell.get)
      if settled then
        s.overscrollState.set 0
      else
        s.overscrollState.set (sign * x')
        loop sign x' v' ns

/-- Settle the stretch band back to rest with the EdgeEffect spring
(ω₀ = 24.657, ζ = 0.98, linear-glide endgame), carrying an initial
overscroll-space velocity `v0` (px/s — a fling absorb passes the
`stretchAbsorbFactor`-boosted residual). Interruptible like `fling`. -/
def settleStretch (s : ScrollState) (v0 : Float32 := 0) : UiTask Unit := do
  s.settleStretchFrom (← s.interrupt) v0

/-- Decay-animate the offset from its current position with initial
`velocity` (px/s, positive = toward the end), driven by the frame clock —
the fling a drag-scroll hands off to on release. Interruptible like
`animateScrollTo` (any newer mutation stands it down at its next frame);
stops early on reaching either end of the range — the residual velocity at
the edge carries into the `overscroll` mode's settle instead: the Cupertino
bounce spring (`.bounce`) or the EdgeEffect stretch absorb (`.stretch`,
velocity ×13 per `ON_ABSORB_VELOCITY_ADJUSTMENT`). (A *nested* fling that
edges out mid-flight bounces locally rather than handing the residual to a
parent, the documented cut alongside mid-flight handoff.) The default curve
is Android's spline decay at mdpi (the drag handler passes the real display
density); pass `ExponentialDecay.spec` for the exponential curve. Mirrors
the fling half of `ScrollableState` + `DefaultFlingBehavior`. -/
partial def fling (s : ScrollState) (velocity : Float32)
    (decay : DecaySpec := SplineDecay.spec {})
    (overscroll : OverscrollMode := .none) : UiTask Unit := do
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
    if target < 0 || target > (← s.maxValueState.cell.get) then
      -- Edge hit: the remaining momentum feeds the mode's band (same claimed
      -- generation — the settle is this fling's tail; the value pins, so
      -- visual continuity puts −v into overscroll space).
      match overscroll with
      | .bounce => s.settleOverscrollFrom myGen (-(decay.velocityAt velocity t))
      | .stretch =>
        s.settleStretchFrom myGen (stretchAbsorbFactor * (-(decay.velocityAt velocity t)))
      | .none => pure ()
    else
      unless t ≥ dur do loop myGen x0 t0 dur

end ScrollState

/-- Remember a `ScrollState` at this composition position. Mirrors
`androidx.compose.foundation.rememberScrollState`. -/
def rememberScrollState (initial : Float32 := 0) : Composable ScrollState :=
  remember (ScrollState.create initial)

/-- The scroll measure block shared by both axes: content measured with the
scroll axis unbounded, viewport = the content size clamped into the incoming
constraints, metrics published, value re-clamped, content placed at
`-value` on the axis. -/
private def scrollLayoutBlock (state : ScrollState) (vertical : Bool)
    (mode : OverscrollMode) : CustomLayout :=
  ⟨fun density c measureInner => do
    -- Cache the ambient density for the wheel handler (`wheelScrollStep`).
    state.densityRef.set density
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
    -- Observed like `value`: a band write re-measures exactly this node.
    -- Only bounce mode translates the placement; the stretch is a draw-time
    -- warp, but the observed read must stay in every mode — it is what turns
    -- each band write into a re-measure (and so a re-recorded frame).
    let over ← state.overscrollState.get
    let off := -(roundHalfUp v')
      + (if mode == .bounce then roundHalfUp over else 0)
    return (size, if vertical then ⟨0, off⟩ else ⟨off, 0⟩)⟩

/-- The scroll container's reveal responder: scroll the minimal amount
(`bringIntoViewDelta`, clamped into range) to make the rect visible,
animated via `animateScrollTo`. An already-visible rect returns no task —
it must not interrupt a running fling. -/
private def scrollBringIntoViewResponder (state : ScrollState) (vertical : Bool) :
    BringIntoViewResponder :=
  ⟨fun rect vp => do
    let (leading, trailing, extent) :=
      if vertical then (rect.top, rect.bottom, vp.height)
      else (rect.left, rect.right, vp.width)
    let v ← state.valueState.cell.get
    let maxV ← state.maxValueState.cell.get
    let target := min (max (v + bringIntoViewDelta leading trailing extent) 0) maxV
    if target == v then return (.zero, none)
    -- The content is about to move opposite the value change.
    let shift := v - target
    return (if vertical then (⟨0, shift⟩ : Offset) else ⟨shift, 0⟩,
            some (state.animateScrollTo target))⟩

/-- The wheel handler shared by both axes: scroll by `wheelScrollStep`
(density-resolved) per notch and consume this axis's delta iff movement
actually happened — the
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
  -- Wheels never rubber-band (AOSP skips edge effects for SOURCE_MOUSE);
  -- snapping also frees a bounce the interrupt just froze.
  if (← state.overscrollState.cell.get) != 0 then state.overscrollState.set 0
  let step := (← state.densityRef.get).dpToPx wheelScrollStep
  let moved ← state.scrollBy ((if vertical then -notches else notches) * step)
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
(a slider) consumes, is left alone. The session is bound to the pointer that
pressed (`PointerEvent.pointerId`) — a second finger landing mid-gesture
runs its own gesture elsewhere and must not corrupt this one's origin or
velocity math.

All motion — origin, slop, drag deltas, velocity samples — is measured in
**root** coordinates (`PointerEvent.positionInRoot`): the localized
`position` shifts whenever an ancestor scrolls this node mid-gesture (the
nested-scroll `follow` below), which would under-count the finger and halve
the handed-off fling velocity.

Nested scroll: whichever container owns the gesture publishes its
unconsumed remainder into the dispatch's leftover cell (see
`PointerEvent.setLeftover`); an outer container whose `track` sees a
consumed move *with* a published leftover `follow`s — consuming the
remainder on its own axis, republishing what it leaves, and flinging a
published end-stop velocity on release — while a consumed move with no
leftover (a slider's) still deadens it. Mirrors the drag half of
`Modifier.scrollable`'s touch handling plus the spirit of its nested-scroll
dispatch.

Overscroll (`mode`, default `.stretch`): dragging past a range end grows the
band with whatever motion *no* ancestor consumed either
(`PointerEvent.onDispatchEnd` — the edge effect belongs to the gesture
owner after its ancestors decline, Android's innermost rule; `follow`
never bands); while the band is live further moves feed it directly
(content pinned at the edge, nothing bubbles out) and a reversal unwinds
it before normal scrolling resumes. In `.bounce` the band is the visible
rubber-banded translation and release springs it back Cupertino-style,
absorbing the gesture velocity; in `.stretch` it is the raw pull distance
(clamped to a viewport, EdgeEffect's `mPullDistance ≤ 1`), release runs the
EdgeEffect spring from rest (AOSP `onRelease`), and an end-stop velocity
absorbs ×13 (`onAbsorb`). A press catches a mid-flight settle like it
catches a fling; a caught band that ends up not owning the gesture (click,
cross-axis, an inner drag) settles on its own. -/
private partial def scrollDragHandler (state : ScrollState) (vertical : Bool)
    (mode : OverscrollMode) (scope : PointerInputScope) : UiTask Unit :=
  idle
where
  axisOf (p : Offset) : Float32 := if vertical then p.y else p.x
  crossOf (p : Offset) : Float32 := if vertical then p.x else p.y
  mkLeftover (axis cross : Float32) : Offset :=
    if vertical then ⟨cross, axis⟩ else ⟨axis, cross⟩
  /-- EdgeEffect's `mPullDistance ≤ 1` in px space. -/
  clampMag (x d : Float32) : Float32 := min (max x (-d)) d
  /-- Scroll this container by the leftover's axis component and republish
  the remainder (the cross axis passes through untouched). -/
  consumeLeftover (ev : PointerEvent) (l : Offset) : IO Unit := do
    let motion := axisOf l
    if motion != 0 then
      let moved ← state.scrollBy (-motion)
      ev.setLeftover (mkLeftover (unconsumedMotion motion moved) (crossOf l))
  /-- Let a caught-but-unclaimed band go: a press froze the spring (the
  catch interrupt), so a gesture that ends without owning the band —
  click, window leave, someone else's drag — must release it. -/
  settleCaught : UiTask Unit := do
    unless mode == .none do
      if (← state.overscrollState.cell.get) != 0 then
        let _ ← UiTask.launch (if mode == .stretch then state.settleStretch 0
                               else state.settleOverscroll 0)
  /-- One owned move: while the band is stretched the motion feeds it in raw
  (pre-band) space — same direction stretches further with nothing
  published (the finger is on the band), a reversal unwinds it and scrolls
  the crossing remainder — otherwise scroll and publish as always; the
  dispatch-end hook then grows the band with whatever motion no ancestor
  consumed either. -/
  dragMove (ev : PointerEvent) (motion cross : Float32) : IO Unit := do
    let o ← if mode == .none then pure 0 else state.overscrollState.cell.get
    let motion ← do
      if o != 0 then
        let d ← state.viewportSizeState.cell.get
        -- Stretch tracks the raw pull 1:1 (the damping is visual, applied at
        -- draw time by `stretchIntensity`); bounce tracks the rubber-banded
        -- displacement through raw space so drags accumulate correctly.
        let raw := (if mode == .stretch then o else rubberBandInverse o d) + motion
        if raw * o > 0 then
          state.overscrollState.set
            (if mode == .stretch then clampMag raw d else rubberBand raw d)
          pure 0
        else
          state.overscrollState.set 0
          pure raw
      else pure motion
    let moved ← state.scrollBy (-motion)
    ev.setLeftover (mkLeftover (unconsumedMotion motion moved) cross)
    unless mode == .none do
      ev.onDispatchEnd fun l? => do
        if let some l := l? then
          let m := axisOf l
          if m != 0 && (← state.maxValueState.cell.get) > 0 then
            let d ← state.viewportSizeState.cell.get
            let o ← state.overscrollState.cell.get
            state.overscrollState.set
              (if mode == .stretch then clampMag (o + m) d
               else rubberBand (rubberBandInverse o d + m) d)
  /-- No gesture in flight: a primary press catches a running fling and arms
  tracking (even when a child consumed it — gesture boundaries stay visible
  to a final-pass observer). The pressing pointer owns the session. -/
  idle : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.eventType == .press && ev.button == some .left then
      let _ ← state.interrupt
      track ev.pointerId ev.positionInRoot
        (VelocityTracker.empty.add ev.timestamp (axisOf ev.positionInRoot))
    else
      idle
  /-- Pressed, still within the slop: decide between click (release first),
  our drag (axis slop first), someone else's gesture (cross slop first or a
  consumed move), and cancel (window leave). Other pointers' events pass
  through untouched. -/
  track (pid : UInt64) (origin : Offset) (vt : VelocityTracker) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then track pid origin vt else
    match ev.eventType with
    | .move =>
      if ← ev.isConsumed then
        -- An inner gesture owns this pointer: an inner scrollable's
        -- published remainder is ours to follow; silence (a slider) means
        -- stand off entirely.
        match ← ev.getLeftover with
        | some l =>
          let _ ← state.interrupt
          consumeLeftover ev l
          settleCaught
          follow pid
        | none => settleCaught; dead pid
      else
        let vt := vt.add ev.timestamp (axisOf ev.positionInRoot)
        let slop := (← scope.density).dpToPx dragScrollSlop
        let d := axisOf ev.positionInRoot - axisOf origin
        if d.abs > slop then
          ev.steal
          ev.consume
          let _ ← state.interrupt
          -- Start from the slop edge, not with a jump over the dead zone.
          dragMove ev (d - (if d > 0 then slop else -slop)) 0
          drag pid ev.positionInRoot vt
        else if (crossOf ev.positionInRoot - crossOf origin).abs > slop then
          settleCaught
          dead pid
        else
          track pid origin vt
    | .release =>
      if ev.button == some .left then settleCaught; idle
      else track pid origin vt
    | .exit => settleCaught; idle
    | _ => track pid origin vt
  /-- Past the slop, gesture stolen: moves scroll (consumed; the unconsumed
  remainder and the untouched cross axis published for outer containers),
  release flings — or, end-stopped, publishes the velocity instead — and
  window leave cancels without a fling. -/
  drag (pid : UInt64) (last : Offset) (vt : VelocityTracker) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then drag pid last vt else
    match ev.eventType with
    | .move =>
      ev.consume
      let a := axisOf ev.positionInRoot
      dragMove ev (a - axisOf last) (crossOf ev.positionInRoot - crossOf last)
      drag pid ev.positionInRoot (vt.add ev.timestamp a)
    | .release =>
      if ev.button == some .left then
        ev.consume
        -- Content moves opposite the pointer; carry that into the fling.
        let pv := vt.velocity ev.timestamp
        let o ← if mode == .none then pure 0 else state.overscrollState.cell.get
        if o != 0 then
          -- The gesture ends on the live band: nothing for the ancestors.
          -- Bounce absorbs the gesture velocity into its spring; stretch
          -- releases from rest (AOSP `EdgeEffect.onRelease` zeroes it).
          ev.setLeftover (mkLeftover 0 0)
          let _ ← UiTask.launch (if mode == .stretch then state.settleStretch 0
                                 else state.settleOverscroll pv)
        else
          let v := -pv
          let can ← if v > 0 then state.canScrollForward
                    else if v < 0 then state.canScrollBackward
                    else pure false
          if can then
            ev.setLeftover (mkLeftover 0 0)
            let den ← scope.density
            let _ ← UiTask.launch
              (state.fling v (SplineDecay.spec (.ofDensity den)) (overscroll := mode))
          else
            -- End-stopped (or still): the fling velocity bubbles out — and
            -- whatever no ancestor flings feeds this stop's band (stretch
            -- absorbs ×13, `EdgeEffect.onAbsorb`).
            ev.setLeftover (mkLeftover pv 0)
            unless mode == .none do
              if (← state.maxValueState.cell.get) > 0 then
                let sched ← UiTask.scheduler
                ev.onDispatchEnd fun l? => do
                  let pv' := (l?.map axisOf).getD 0
                  if pv' != 0 then
                    let _ ← sched.launch
                      (if mode == .stretch then
                        state.settleStretch (stretchAbsorbFactor * pv')
                       else state.settleOverscroll pv')
        idle
      else
        drag pid last vt
    | .exit => settleCaught; idle
    | _ => drag pid last vt
  /-- An inner scrollable owns the gesture but ran out of range: consume the
  leftover it publishes on this container's axis (republishing the rest, so
  a third container cascades) and fling a published end-stop velocity on
  release — leaving it for outer containers when this one is end-stopped
  too. Never steals: the inner keeps the gesture. -/
  follow (pid : UInt64) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then follow pid else
    match ev.eventType with
    | .move =>
      if let some l ← ev.getLeftover then consumeLeftover ev l
      follow pid
    | .release =>
      if ev.button == some .left then
        if let some l ← ev.getLeftover then
          let pv := axisOf l
          let v := -pv
          let can ← if v > 0 then state.canScrollForward
                    else if v < 0 then state.canScrollBackward
                    else pure false
          if can then
            ev.setLeftover (mkLeftover 0 (crossOf l))
            let den ← scope.density
            let _ ← UiTask.launch
              (state.fling v (SplineDecay.spec (.ofDensity den)) (overscroll := mode))
        idle
      else follow pid
    | .exit => idle
    | _ => follow pid
  /-- This gesture belongs to someone else: sit out the session pointer's
  gesture until it ends (other pointers' events pass through). -/
  dead (pid : UInt64) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then dead pid else
    match ev.eventType with
    | .release => if ev.button == some .left then idle else dead pid
    | .exit => idle
    | _ => dead pid

namespace Modifier

/-- The stretch-mode draw element: reads the raw band + viewport (plain,
non-observed — the layout block's observed read already re-records the frame
on every band write) and derives the damped warp intensity on the container's
axis. -/
private def stretchRead (state : ScrollState) (vertical : Bool) :
    IO (Float32 × Float32) := do
  let s := stretchIntensity (← state.overscrollState.cell.get)
    (← state.viewportSizeState.cell.get)
  return if vertical then (0, s) else (s, 0)

/-- Make the content scrollable vertically: content measures with unbounded
height, the container reports `min(content, incoming max)`, clips to its
bounds, offsets the content by `-state.value`, consumes wheel events when
it can scroll in their direction, and drag-scrolls with a fling on release
(see `scrollDragHandler`). `overscroll` picks the edge visual (wheel
scrolling never overscrolls): `.stretch` (default) is Android 12+'s
`EdgeEffect` content warp, `.bounce` the Cupertino translation rubber band,
`.none` a hard stop. Mirrors
`androidx.compose.foundation.verticalScroll(state)`. -/
def verticalScroll (state : ScrollState) (m : Modifier := {})
    (overscroll : OverscrollMode := .stretch) : Modifier :=
  let m := m.onScroll (scrollWheelHandler state true)
  |>.pointerInput (mixKeys (stringKey "Compose.Modifier.dragScroll.v")
        (mixKeys state.id overscroll.key))
      (scrollDragHandler state true overscroll) (pass := .final)
  |>.bringIntoView (mixKeys (stringKey "Compose.Modifier.bringIntoView.v") state.id)
      (scrollBringIntoViewResponder state true)
  |>.clip .rectangle
  -- The stretch layer sits between the scroll clip (which crops the warp)
  -- and the content the customLayout places.
  let m := if overscroll == .stretch then
    m.stretchLayer (mixKeys (stringKey "Compose.Modifier.stretchOverscroll") state.id)
      (stretchRead state true)
  else m
  m.customLayout (mixKeys (stringKey "Compose.Modifier.verticalScroll")
      (mixKeys state.id overscroll.key))
    (scrollLayoutBlock state true overscroll)

/-- Horizontal counterpart of `verticalScroll`. Mirrors
`androidx.compose.foundation.horizontalScroll(state)`. -/
def horizontalScroll (state : ScrollState) (m : Modifier := {})
    (overscroll : OverscrollMode := .stretch) : Modifier :=
  let m := m.onScroll (scrollWheelHandler state false)
  |>.pointerInput (mixKeys (stringKey "Compose.Modifier.dragScroll.h")
        (mixKeys state.id overscroll.key))
      (scrollDragHandler state false overscroll) (pass := .final)
  |>.bringIntoView (mixKeys (stringKey "Compose.Modifier.bringIntoView.h") state.id)
      (scrollBringIntoViewResponder state false)
  |>.clip .rectangle
  let m := if overscroll == .stretch then
    m.stretchLayer (mixKeys (stringKey "Compose.Modifier.stretchOverscroll") state.id)
      (stretchRead state false)
  else m
  m.customLayout (mixKeys (stringKey "Compose.Modifier.horizontalScroll")
      (mixKeys state.id overscroll.key))
    (scrollLayoutBlock state false overscroll)

end Modifier

end Compose

end
