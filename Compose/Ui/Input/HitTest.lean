module

public import Compose.Ui.Node
public meta import Compose.Ui.Node

public section

namespace Compose

/-!
# Pointer hit testing and dispatch (`Compose/Ui/Input/HitTest.lean`)

The `LayoutNode`-tree half of the pointer story (the event/queue types live
in `Compose.Ui.Input.Pointer`, below `Modifier`):

* **Hit testing** (`LayoutNode.hitTest`) walks the tree from the root,
  children in *reverse* draw order (later siblings are on top — the first
  child subtree containing a hit wins over lower siblings), respecting each
  wrapper's coordinates and clip bounds: a `Modifier.clip` element
  geometrically excludes everything inner (inner elements and children) via
  `RoundRect.contains`, exactly the shape the draw walk clips to. The result
  is the hit path root→leaf. Mirrors `LayoutNode.hitTest` +
  `NodeCoordinator.hitTest`.

* **Dispatch** (`dispatchToPath`) delivers an event to the pointer elements
  along the path leaf→root (bubbling), innermost element first within a node,
  honoring the per-dispatch consumed flag. Scroll events carry a per-dispatch
  *remaining delta*: each `Modifier.onScroll` handler sees what is left and
  returns what it consumed per axis, so nested horizontal + vertical
  scrollables split one diagonal wheel event; the event counts as consumed
  once the remainder hits zero. Positions are localized to each element's
  wrapper region. Mirrors the main pass of Compose's pointer-input dispatch.

* **Reconcile** (`LayoutNode.reconcilePointerInputs`) is where
  `Modifier.pointerInput` coroutines attach to the node lifecycle: `Layout`'s
  update phase calls it after every modifier update. There are no dedicated
  attach hooks on `LayoutNode`, so lifecycle is driven from the update-diff
  (documented design): states match the chain's `pointerInput` elements
  *positionally* (like slot memoization); a key change (or an element
  appearing) cancels the old coroutine and launches the new handler on the
  ambient scheduler; disappearing elements are cancelled; node removal
  cancels everything via `severParentLinks` (the applier's detach path).
-/

/-- One node on a hit path: the node plus the chain indices of the
pointer/focus elements whose (clip-respecting) regions contain the point.
Mirrors an entry of Compose's `HitTestResult`. -/
structure HitTarget where
  node : LayoutNode
  /-- Hit chain indices into `node`'s `modifier.elems` (pointer/focus only). -/
  elems : Array Nat
  deriving Inhabited

namespace LayoutNode

/-- Origin of the node's outer box in root coordinates (accumulated parent
placements and content offsets). Mirrors
`LayoutCoordinates.positionInRoot`. -/
partial def originInRoot (n : LayoutNode) : IO Offset := do
  let d ← n.data
  match d.parent with
  | none => return .zero
  | some p =>
    return (← p.originInRoot) + (← p.data).contentOffset.toOffset + d.position.toOffset

/-- Whether `n` is `anc` itself or below it, by walking `n`'s parent chain
(node identity is `nodeId`). With `anc` a tree root this is an *attachment*
test: a node past `severParentLinks` reaches no root. -/
partial def isDescendantOf (n anc : LayoutNode) : IO Bool := do
  if (← n.nodeId) == (← anc.nodeId) then return true
  match (← n.data).parent with
  | some p => p.isDescendantOf anc
  | none => return false

/-- Hit-test one node's own chain at `p` (node-outer coordinates): the hit
pointer/focus element indices, and whether the point survives every `clip`
so children may be hit. Elements *outer* to a failed clip keep their hits;
everything inner is excluded. -/
private def hitChain (d : LayoutNodeData) (p : Offset) : Array Nat × Bool := Id.run do
  let mut hits := #[]
  for rd in d.resolvedDraws do
    let local' := p - rd.offset.toOffset
    match d.modifier.elems[rd.elemIdx]? with
    | some (.draw (.clip shape)) =>
      unless (shape.toRoundRect rd.size.toSize d.density).contains local' do
        return (hits, false)
    | some (.pointer _) | some (.focus _) =>
      if (Rect.ofSize rd.size.toSize).contains local' then
        hits := hits.push rd.elemIdx
    | _ => pure ()
  return (hits, true)

/-- Hit-test the subtree at `p` (this node's outer coordinates), producing
the hit path root→leaf (see the module docstring for the z-order and clip
rules). -/
partial def hitTest (n : LayoutNode) (p : Offset) : IO (Array HitTarget) := do
  let d ← n.data
  -- A non-hit-testable node is transparent to the pointer, subtree and all
  -- (an inert overlay layer during a dropdown's exit animation).
  unless d.hitTestable do return #[]
  let (elems, open') := hitChain d p
  let self : Array HitTarget := if elems.isEmpty then #[] else #[{ node := n, elems }]
  unless open' do return self
  let q := p - d.contentOffset.toOffset
  for i in [0:d.children.size] do
    let ch := d.children[d.children.size - 1 - i]!
    let sub ← ch.hitTest (q - (← ch.data).position.toOffset)
    unless sub.isEmpty do return self ++ sub
  return self

end LayoutNode

/-- Deliver `ev` to the pointer elements of one hit target. `rootPos` is the
event position in root coordinates; each element receives it localized to
its wrapper region. Consumption gates per element: main-pass elements are
skipped once the event is consumed, `PointerPass.final` observers receive
every event (and check `isConsumed` themselves). `pointerInput` elements get
the event through their queue (waking a parked `awaitEvent` synchronously);
`onScroll` handlers run for `scroll` events against `scrollRemaining` (the
per-dispatch leftover delta, created by `dispatchToPath`): each returns what
it consumed per axis, and the event counts as consumed when the remainder
reaches zero. Given `stealSlot`, each delivered event's `steal` records the
receiving node (the router turns it into a capture takeover — see
`PointerEvent.steal`). -/
def HitTarget.deliver (t : HitTarget) (ev : PointerEvent) (rootPos : Offset)
    (scrollRemaining : Option (IO.Ref Offset) := none)
    (stealSlot : Option (IO.Ref (Option Nat)) := none) : IO Unit := do
  let d ← t.node.data
  let origin ← t.node.originInRoot
  -- Innermost element first (bubbling starts at the leaf-most handler).
  for i in [0:t.elems.size] do
    let consumed ← ev.isConsumed
    let idx := t.elems[t.elems.size - 1 - i]!
    let offset := (d.resolvedDraws.find? (·.elemIdx == idx)).map (·.offset.toOffset) |>.getD .zero
    let localPos := rootPos - origin - offset
    match d.modifier.elems[idx]? with
    | some (.pointer (.input _ pass _)) =>
      if pass == .final || !consumed then
        -- Coroutines observing a partially consumed scroll see the remainder.
        let delta ← match scrollRemaining with
          | some rem => rem.get
          | none => pure ev.scrollDelta
        let steal ← match stealSlot with
          | some slot => do
            let nid ← t.node.nodeId
            pure (slot.set (some nid))
          | none => pure ev.steal
        for st in d.pointerInputs do
          if (← st.elemIdx.get) == idx then
            st.offer { ev with position := localPos, positionInRoot := rootPos
                               scrollDelta := delta, steal }
    | some (.pointer (.onScroll f)) =>
      if !consumed && ev.eventType == .scroll then
        match scrollRemaining with
        | some rem =>
          let delta ← rem.get
          if delta != .zero then
            let used ← f delta
            let left := delta - used
            rem.set left
            if left == .zero then ev.consume
        | none =>
          -- Defensive: without a remainder ref, any consumption is total.
          if (← f ev.scrollDelta) != .zero then ev.consume
    | _ => pure ()

/-- Dispatch `ev` (position in root coordinates) along `path` **leaf→root**;
returns whether some handler consumed. Consumption gates main-pass elements
(but the sweep continues so `PointerPass.final` observers outer to the
consumer still see the event). Scroll events get a per-dispatch
remaining-delta cell so `onScroll` handlers along the path each consume
their own axis; `stealSlot` (captured moves) collects a capture-takeover
request (see `HitTarget.deliver`). The entry point the input router (and
tests) drive with translated events. -/
def dispatchToPath (path : Array HitTarget) (ev : PointerEvent)
    (stealSlot : Option (IO.Ref (Option Nat)) := none) : IO Bool := do
  let consumed ← IO.mkRef false
  let ev := { ev with consume := consumed.set true, isConsumed := consumed.get }
  -- Moves and releases carry the nested-scroll leftover cell (the drag
  -- analog of scrollRemaining below) and the dispatch-end finalizer slot;
  -- the closures ride the event through `deliver`'s copies, so handlers
  -- along the path share one cell.
  let leftover ← IO.mkRef (none : Option Offset)
  let finalizer ← IO.mkRef (none : Option (Option Offset → IO Unit))
  let ev := match ev.eventType with
    | .move | .release =>
      { ev with setLeftover := fun o => leftover.set (some o)
                getLeftover := leftover.get
                onDispatchEnd := fun f => finalizer.set (some f) }
    | _ => ev
  let scrollRemaining ←
    if ev.eventType == .scroll then some <$> IO.mkRef ev.scrollDelta
    else pure none
  for i in [0:path.size] do
    (path[path.size - 1 - i]!).deliver ev ev.position scrollRemaining stealSlot
  -- The sweep is synchronous (parked `awaitEvent`s wake inline), so a
  -- registered finalizer runs here with the surviving leftover.
  if let some f ← finalizer.get then f (← leftover.get)
  consumed.get

namespace LayoutNode

/-- Reconcile the node's running `pointerInput` coroutines with its current
modifier chain (see the module docstring — this is the attach half of the
element lifecycle; `severParentLinks` is the detach half). States are matched
to the chain's `pointerInput` elements by ordinal position: an unchanged key
keeps the running coroutine (Compose semantics — the original handler lambda
keeps running; a changed handler with the same key is *not* restarted); a
changed key cancels and relaunches; extra old states are cancelled. Throws
when handlers exist but no scheduler is ambient. -/
def reconcilePointerInputs (n : LayoutNode) (sched? : Option Scheduler) : IO Unit := do
  let d ← n.data
  let wanted := d.modifier.pointerInputElems
  if wanted.isEmpty && d.pointerInputs.isEmpty then return
  let mut states : Array PointerInputState := #[]
  for i in [0:wanted.size] do
    let (idx, key, handler) := wanted[i]!
    let old? := d.pointerInputs[i]?
    match old? with
    | some old =>
      if old.key == key then
        old.elemIdx.set idx
        states := states.push old
      else
        old.cancel
        states := states.push (← launch idx key handler)
    | none =>
      states := states.push (← launch idx key handler)
  (d.pointerInputs.extract wanted.size d.pointerInputs.size).forM (·.cancel)
  n.modifyData fun x => { x with pointerInputs := states }
where
  /-- Launch `handler` for the element at `idx` on the ambient scheduler
  (started by the loop's next `runDue`, like a `LaunchedEffect`). -/
  launch (idx : Nat) (key : UInt64) (handler : PointerInputScope → UiTask Unit) :
      IO PointerInputState := do
    let some sched := sched?
      | throw (IO.userError
          "Compose: no ambient Scheduler — Modifier.pointerInput needs a \
           LocalScheduler provider (runApp installs one)")
    let st ← PointerInputState.create key idx
    let scope : PointerInputScope :=
      { state := st
        getDensity := do return (← n.data).density
        getSize := do
          let dd ← n.data
          let i ← st.elemIdx.get
          match dd.resolvedDraws.find? (·.elemIdx == i) with
          | some rd => return rd.size
          | none => return dd.size }
    st.job.set (some (← sched.launch (handler scope)))
    return st

end LayoutNode

end Compose

end
