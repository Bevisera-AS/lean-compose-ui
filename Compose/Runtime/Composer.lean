import Compose.Runtime.SlotVal
import Compose.Runtime.State
import Compose.Runtime.Applier

namespace Compose

/-!
# Composer and group tree

The composition is a mutable tree of groups (`IO.Ref GroupData` cells, boxed
through `SlotVal` to tie the `Group`/`GroupData` recursive knot), mirroring
`androidx.compose.runtime.Composer` + `SlotTable` semantics without the
gap-buffer representation.

Group matching on recomposition is Compose's algorithm: at each child
position, if the next existing child's key matches, enter it; otherwise
search the remaining siblings for the key (conditional appearance and
`keyed`-driven reorder → an applier `move`); missing → insert; leftovers at
group end are disposed (remember-observers forgotten depth-first, emitted
nodes removed via the applier at exact indices).

Emitted-node bookkeeping: every group stores `nodes`, the number of nodes its
subtree contributes to the nearest ancestor node ("node parent"): `1` for a
node group, the sum over children otherwise. During composition each open
group's `Frame.nodeIndex` tracks how many nodes precede the cursor inside the
current node parent, which is exactly the applier index for the next
insert/remove/move.

A throw escaping composable content unwinds the open groups (`abortTo`):
freshly inserted groups are undone and severed, surviving open scopes are
invalidated for retry, so the applier and the group tree always agree.
Pass-level rollback (pending effects, `composed`) lives in
`Compose.Runtime.Recomposer` — see its module docstring for the contract.
-/

/-- Mix two group keys (splitmix-style multiply-add); used to derive child
keys for `keyed` and provider groups. Mirrors the key-mixing of the Compose
compiler plugin. -/
def mixKeys (a b : UInt64) : UInt64 := a * 0x9E3779B97F4A7C15 + b

#guard mixKeys 1 2 != mixKeys 2 1
#guard mixKeys 0 5 != mixKeys 0 6
#guard mixKeys 3 0 != mixKeys 0 3

/-- Reserved group key for emitted-node groups (`emitNode`). Node groups all
share this key (like Compose's `nodeKey`); distinguish node kinds at the same
position with an enclosing `withGroup`/branch group. -/
def nodeGroupKey : UInt64 := 0x6e6f6465

/-- Salt mixed into `keyed` data keys so they don't collide with positional
source keys. -/
def keyedGroupSalt : UInt64 := 0x6b657965

/-- Salt mixed into `CompositionLocalProvider` group keys. -/
def providerGroupSalt : UInt64 := 0x70726f76

/-- Lifecycle callbacks for values remembered in the composition. Callbacks
are deferred until the composition applies successfully; forgotten callbacks
of removed groups run depth-first, before newly-remembered callbacks.
Mirrors `androidx.compose.runtime.RememberObserver`. -/
structure RememberObserver where
  onRemembered : IO Unit
  onForgotten : IO Unit

/-- One positional memoization slot of a group. -/
structure Slot where
  val : SlotVal
  /-- Present when the slot participates in the remember lifecycle. -/
  observer : Option RememberObserver := none

instance : Inhabited Slot := ⟨{ val := default }⟩

/-- A group in the composition tree. The box always holds an
`IO.Ref GroupData` (this is one of the audited `SlotVal` uses, see
`Compose.Runtime.SlotVal`); the indirection ties the recursive knot between
`Group` and `GroupData`. -/
structure Group where
  box : SlotVal
  deriving Inhabited

/-- Persistent map of provided `CompositionLocal` values, keyed by local id.
Prepend-on-insert gives lexical shadowing. Mirrors the `CompositionLocalMap`
carried by Compose's composer. -/
structure LocalMap where
  entries : List (Nat × SlotVal) := []

instance : Inhabited LocalMap := ⟨{}⟩

namespace LocalMap

/-- The empty scope (only defaults visible). -/
def empty : LocalMap := {}

/-- Bind `id` to `v`, shadowing any outer binding. -/
def insert (m : LocalMap) (id : Nat) (v : SlotVal) : LocalMap :=
  ⟨(id, v) :: m.entries⟩

/-- Innermost binding for `id`, if provided. -/
def find? (m : LocalMap) (id : Nat) : Option SlotVal :=
  m.entries.lookup id

#guard ((empty.insert 1 (SlotVal.mk "a")).find? 1 |>.map (·.get! (α := String))) == some "a"
#guard ((empty.insert 1 (SlotVal.mk "a")).insert 1 (SlotVal.mk "b") |>.find? 1
          |>.map (·.get! (α := String))) == some "b"
#guard (empty.insert 1 (SlotVal.mk "a") |>.find? 2 |>.isNone)

end LocalMap

/-- The restartable unit of recomposition: a group that can re-run its body in
place. Mirrors `androidx.compose.runtime.RecomposeScope`. -/
structure RecomposeScope where
  id : Nat
  /-- The restartable group this scope re-runs. -/
  group : Group
  /-- Re-invokes the composable body with the arguments of its latest
  execution (stored by `endRestartGroup`). -/
  rerun : IO.Ref (IO Unit)
  /-- `false` = invalidated, pending recomposition. -/
  valid : IO.Ref Bool
  /-- Set when the scope's group is removed from the composition. -/
  disposed : IO.Ref Bool
  /-- Two-way registration on the states the latest run read. -/
  reads : ObservationRegistry
  /-- `CompositionLocal` scope captured at the latest run, so a standalone
  re-run resolves the same provided values. -/
  locals : IO.Ref LocalMap
  /-- Holds the enqueue-on-invalidate action run by `reads.dep.invalidate`.
  The action closes over the scope itself, so it must be reset to a no-op
  when the scope's group is removed — Lean's runtime is pure reference
  counting, and this closure is the scope's self-cycle. -/
  invalidateCell : IO.Ref (IO Unit)

/-- Mark the scope invalid and enqueue it on its composer's invalidation
queue (no-op once disposed). Mirrors `RecomposeScope.invalidate`. -/
def RecomposeScope.invalidate (s : RecomposeScope) : IO Unit :=
  s.reads.dep.invalidate

/-- Tear down a scope whose group left the composition: mark it disposed,
unregister its state reads, and drop every closure that cycles back to the
scope or retains the composer (invalidate action, rerun, captured locals). -/
def RecomposeScope.sever (s : RecomposeScope) : IO Unit := do
  s.disposed.set true
  s.reads.clear
  s.invalidateCell.set (pure ())
  s.rerun.set (pure ())
  s.locals.set .empty

/-- Mutable payload of one group. -/
structure GroupData where
  /-- Source-position key (macro-injected) or user key hash. -/
  key : UInt64
  /-- Unique identity (parent-child searches, queue dedup). -/
  gid : Nat
  /-- Remembered values, positional. -/
  slots : Array Slot := #[]
  /-- Sub-groups in order. -/
  children : Array Group := #[]
  /-- Emitted nodes this subtree contributes to its node parent: `1` for a
  node group, the sum over children otherwise. -/
  nodes : Nat := 0
  /-- Present on restartable groups. -/
  scope : Option RecomposeScope := none
  parent : Option Group := none
  /-- Whether this group emitted a node (`emitNode`). -/
  isNode : Bool := false
  /-- The emitted node, when `isNode`. -/
  node : Option NodeVal := none

instance : Inhabited GroupData := ⟨{ key := 0, gid := 0 }⟩

namespace Group

/-- The underlying mutable cell (the box invariantly holds an
`IO.Ref GroupData`). -/
def cell (g : Group) : IO.Ref GroupData := g.box.get!

/-- Read the group's data. -/
def data (g : Group) : IO GroupData := g.cell.get

/-- Mutate the group's data. -/
def modifyData (g : Group) (f : GroupData → GroupData) : IO Unit := g.cell.modify f

/-- Allocate a fresh group. -/
def create (d : GroupData) : IO Group :=
  return ⟨SlotVal.mk (← IO.mkRef d)⟩

end Group

/-- Sever the reference cycles inside a subtree that left the composition so
plain reference counting can free it (Lean's runtime has no cycle collector):
parent↔child links, group↔scope links, remembered slots, and emitted-node
references. Only for removed groups — matching and relocation need these
edges on kept ones. Runs after `Composer.collectDisposals` (forget thunks
close over what they need, not over the slots). -/
partial def severSubtree (g : Group) : IO Unit := do
  let gd ← g.data
  if let some s := gd.scope then
    s.sever
  gd.children.forM severSubtree
  g.modifyData fun d =>
    { d with parent := none, scope := none, children := #[], slots := #[],
             node := none, nodes := 0 }

/-- Number of nodes a subtree has actually inserted into its node parent.
`nodes` counts are only finalized at `endGroup`, so removal after an aborted
pass counts what is really in the applier: a node group's `node` is recorded
at insert time (`emitNode`) and cleared by `severSubtree` on removal. -/
partial def liveNodeCount (g : Group) : IO Nat := do
  let gd ← g.data
  if gd.isNode then
    return if gd.node.isSome then 1 else 0
  else
    gd.children.foldlM (fun acc ch => return acc + (← liveNodeCount ch)) 0

/-- One open group during composition: the group plus its child/slot cursors.

`nodeIndex` is the number of emitted nodes preceding the child cursor within
the current node parent — the applier index for the next node operation. -/
structure Frame where
  group : Group
  childCursor : Nat := 0
  slotCursor : Nat := 0
  nodeIndex : Nat := 0
  /-- The group was freshly inserted this pass: children/slots are appended
  without matching. -/
  inserting : Bool := false
  deriving Inhabited

/-- The mutable composition context threaded through every composable.
Mirrors `androidx.compose.runtime.Composer`. -/
structure Composer where
  applier : NodeApplier
  /-- Root of the group tree (key 0, never disposed). -/
  rootGroup : Group
  /-- Stack of open groups; the top is the current group. -/
  frames : IO.Ref (Array Frame)
  /-- Stack of applier parents; bottom is `applier.root`, `emitNode` pushes. -/
  nodeParents : IO.Ref (Array NodeVal)
  /-- Innermost active restart scopes; reads attribute to the top. -/
  scopeStack : IO.Ref (Array RecomposeScope)
  /-- Set by the recomposer to make the next `startGroup` enter this exact
  group (with the given base node index) — how a scope re-runs in place. -/
  pendingEnter : IO.Ref (Option (Group × Nat))
  /-- Whether the current pass is a standalone scope re-run (node-count deltas
  then propagate to ancestor groups when the scope's frame closes). -/
  standaloneRerun : IO.Ref Bool
  /-- Currently provided `CompositionLocal` values. -/
  locals : IO.Ref LocalMap
  /-- Scopes invalidated since the last drain. -/
  invalidations : IO.Ref (Array RecomposeScope)
  /-- Deferred `onForgotten`s, collected in document order, dispatched in
  reverse (children before parents) after a successful apply. -/
  pendingForgets : IO.Ref (Array (IO Unit))
  /-- Deferred `onRemembered`s, dispatched in order after forgets. -/
  pendingRemembers : IO.Ref (Array (IO Unit))
  /-- Deferred `SideEffect`s, dispatched last. -/
  pendingSideEffects : IO.Ref (Array (IO Unit))
  /-- Observer called whenever a scope is invalidated (enqueued for
  recomposition). The M5 app shell points this at its needs-frame flag so any
  state write schedules a frame — the composition half of Compose's
  `Recomposer` waking its apply loop. Defaults to a no-op. -/
  onInvalidate : IO.Ref (IO Unit)

/-- The composable monad: an effectful computation with access to the ambient
composer. Mirrors `@Composable` functions receiving `$composer`. -/
abbrev Composable (α : Type) := ReaderT Composer IO α

namespace Composer

/-- Fresh composer over an erased applier. -/
def create (applier : NodeApplier) : IO Composer :=
  return { applier
           rootGroup := ← Group.create { key := 0, gid := ← freshId }
           frames := ← IO.mkRef #[]
           nodeParents := ← IO.mkRef #[]
           scopeStack := ← IO.mkRef #[]
           pendingEnter := ← IO.mkRef none
           standaloneRerun := ← IO.mkRef false
           locals := ← IO.mkRef .empty
           invalidations := ← IO.mkRef #[]
           pendingForgets := ← IO.mkRef #[]
           pendingRemembers := ← IO.mkRef #[]
           pendingSideEffects := ← IO.mkRef #[]
           onInvalidate := ← IO.mkRef (pure ()) }

private def topFrame (c : Composer) : IO Frame := do
  match (← c.frames.get).back? with
  | some f => return f
  | none => throw <| IO.userError "Compose: no open group (composition misuse)"

private def modifyTopFrame (c : Composer) (f : Frame → Frame) : IO Unit :=
  c.frames.modify fun fs =>
    if fs.isEmpty then fs else fs.set! (fs.size - 1) (f fs.back!)

private def pushFrame (c : Composer) (fr : Frame) : IO Unit :=
  c.frames.modify (·.push fr)

private def currentNodeParent (c : Composer) : IO NodeVal := do
  match (← c.nodeParents.get).back? with
  | some n => return n
  | none => throw <| IO.userError "Compose: node parent stack empty"

/-- Create a `RecomposeScope` for `g`, wired to this composer's invalidation
queue (invalidations dedup by scope id). -/
private def freshScope (c : Composer) (g : Group) : IO RecomposeScope := do
  let invalidateCell ← IO.mkRef (pure () : IO Unit)
  let scope : RecomposeScope :=
    { id := ← freshId, group := g
      rerun := ← IO.mkRef (pure ())
      valid := ← IO.mkRef true
      disposed := ← IO.mkRef false
      reads := ← ObservationRegistry.create
        { id := ← freshId, invalidate := do (← invalidateCell.get) }
      locals := ← IO.mkRef .empty
      invalidateCell }
  invalidateCell.set do
    unless ← scope.disposed.get do
      scope.valid.set false
      c.invalidations.modify fun q =>
        if q.any (·.id == scope.id) then q else q.push scope
      (← c.onInvalidate.get)
  return scope

/-- Collect disposal work for a removed subtree in document order: a group's
remembered slots, then children. `dispatchEffects` runs the collected forgets
in reverse, so children's callbacks fire before their parents' — Compose's
reverse-remember-order forgetting. Scope teardown and cycle severing are
`severSubtree`'s job, run after the applier removal that still needs the
subtree intact. -/
partial def collectDisposals (c : Composer) (g : Group) : IO Unit := do
  let gd ← g.data
  for s in gd.slots do
    if let some obs := s.observer then
      c.pendingForgets.modify (·.push obs.onForgotten)
  gd.children.forM (c.collectDisposals ·)

/-- Dispatch deferred lifecycle events after a successful apply: forgotten
callbacks (reverse collection order: depth-first, removed groups first), then
newly-remembered callbacks, then side effects. Mirrors
`androidx.compose.runtime`'s `RememberEventDispatcher`. -/
def dispatchEffects (c : Composer) : IO Unit := do
  let forgets ← c.pendingForgets.modifyGet fun a => (a, #[])
  forgets.reverse.forM id
  let remembers ← c.pendingRemembers.modifyGet fun a => (a, #[])
  remembers.forM id
  let effects ← c.pendingSideEffects.modifyGet fun a => (a, #[])
  effects.forM id

/-- After a standalone scope re-run changed a subtree's node count, patch the
ancestor chain's `nodes` up to (excluding) the nearest node group or root.
(Nested recomposition keeps counts via `endGroup` as frames close; only
standalone re-runs need explicit propagation.) -/
partial def propagateNodeDelta (g : Group) (oldN newN : Nat) : IO Unit := do
  if oldN == newN then return
  match (← g.data).parent with
  | none => return
  | some p =>
    let pd ← p.data
    if pd.isNode then return
    let pNew := pd.nodes + newN - oldN
    p.modifyData fun d => { d with nodes := pNew }
    propagateNodeDelta p pd.nodes pNew

/-- Open the child group with key `key` at the current cursor, using
Compose's matching algorithm (match / relocate / insert; see module doc). -/
def startGroup (c : Composer) (key : UInt64) (isNode : Bool) : IO Group := do
  -- Standalone scope re-run: enter the scope's own group directly.
  if let some (g, base) ← c.pendingEnter.get then
    c.pendingEnter.set none
    c.pushFrame { group := g, nodeIndex := base }
    return g
  let f ← c.topFrame
  let insertFresh : IO Group := do
    let g ← Group.create { key, gid := ← freshId, isNode, parent := some f.group }
    f.group.modifyData fun d =>
      { d with children := d.children.insertIdx! f.childCursor g }
    c.pushFrame { group := g, nodeIndex := if isNode then 0 else f.nodeIndex,
                  inserting := true }
    return g
  if f.inserting then
    insertFresh
  else
    let gd ← f.group.data
    let enter (g : Group) : IO Group := do
      let child ← g.data
      c.pushFrame { group := g, nodeIndex := if child.isNode then 0 else f.nodeIndex }
      return g
    if h : f.childCursor < gd.children.size then
      if (← gd.children[f.childCursor].data).key == key then
        enter gd.children[f.childCursor]
      else
        -- Search the remaining siblings (conditional appearance / reorder).
        let mut found : Option Nat := none
        for j in [f.childCursor + 1 : gd.children.size] do
          if (← gd.children[j]!.data).key == key then
            found := some j
            break
        match found with
        | none => insertFresh
        | some j =>
          -- Relocate group j to the cursor; move its emitted nodes along.
          let moved := gd.children[j]!
          let movedNodes := (← moved.data).nodes
          let mut gap := 0
          for i in [f.childCursor : j] do
            gap := gap + (← gd.children[i]!.data).nodes
          if movedNodes > 0 && gap > 0 then
            c.applier.move (← c.currentNodeParent)
              (f.nodeIndex + gap) f.nodeIndex movedNodes
          f.group.modifyData fun d =>
            { d with children := (d.children.eraseIdx! j).insertIdx! f.childCursor moved }
          enter moved
    else
      insertFresh

/-- Close the current group: dispose leftover children (forgotten callbacks
collected depth-first, emitted nodes removed via the applier at exact
indices) and leftover slots, recompute the group's node count, and advance
the parent frame's cursors. -/
def endGroup (c : Composer) : IO Unit := do
  let fs ← c.frames.get
  let some f := fs.back?
    | throw <| IO.userError "Compose: endGroup without startGroup"
  c.frames.set fs.pop
  let gd ← f.group.data
  -- Dispose leftover children: all matched/created ones precede the cursor.
  if f.childCursor < gd.children.size then
    let np ← c.currentNodeParent
    for j in [f.childCursor : gd.children.size] do
      let ch := gd.children[j]!
      c.collectDisposals ch
      -- Count what is actually in the applier (`nodes` can be stale for a
      -- subtree an aborted pass touched).
      let n ← liveNodeCount ch
      if n > 0 then
        c.applier.remove np f.nodeIndex n
      severSubtree ch
  -- Dispose leftover slots.
  for i in [f.slotCursor : gd.slots.size] do
    if let some obs := gd.slots[i]!.observer then
      c.pendingForgets.modify (·.push obs.onForgotten)
  -- Recompute the node count over the kept children.
  let kept := gd.children.take f.childCursor
  let mut count := 0
  for ch in kept do
    count := count + (← ch.data).nodes
  let newNodes := if gd.isNode then 1 else count
  f.group.modifyData fun d =>
    { d with children := kept, slots := d.slots.take f.slotCursor, nodes := newNodes }
  if (← c.frames.get).isEmpty then
    if ← c.standaloneRerun.get then
      propagateNodeDelta f.group gd.nodes newNodes
  else
    c.modifyTopFrame fun pf =>
      { pf with childCursor := pf.childCursor + 1, nodeIndex := pf.nodeIndex + newNodes }

/-- Index of the child with identity `gid` in `p`'s children, if present. -/
private def childIndexOf (p : Group) (gid : Nat) : IO (Option Nat) := do
  let pd ← p.data
  for j in [0 : pd.children.size] do
    if (← pd.children[j]!.data).gid == gid then
      return some j
  return none

/-- Unwind open groups after an exception escaped composable content, popping
frames down to `depth`: groups freshly inserted by the failed pass are undone
(applier nodes removed, group erased from its parent, subtree severed), and
restart scopes of surviving open groups are invalidated so a retry re-runs
them instead of skipping over half-updated content. Leaves the applier and
the group tree agreeing (no ghost nodes); the caller rethrows. -/
def abortTo (c : Composer) (depth : Nat) : IO Unit := do
  while (← c.frames.get).size > depth do
    let fs ← c.frames.get
    let f := fs.back!
    c.frames.set fs.pop
    let gd ← f.group.data
    if f.inserting then
      let n ← liveNodeCount f.group
      if n > 0 then
        -- The parent's cursor still points at this group's first node (it
        -- only advances at child `endGroup`).
        let base := ((← c.frames.get).back?.map (·.nodeIndex)).getD 0
        c.applier.remove (← c.currentNodeParent) base n
      if let some p := gd.parent then
        if let some j ← childIndexOf p gd.gid then
          p.modifyData fun d => { d with children := d.children.eraseIdx! j }
      severSubtree f.group
    else if let some s := gd.scope then
      s.valid.set false

private def advanceSlot (c : Composer) : IO Unit :=
  c.modifyTopFrame fun fr => { fr with slotCursor := fr.slotCursor + 1 }

/-- Positional memoization: run `init` on first composition, return the
stored value afterwards. Mirrors `androidx.compose.runtime.Composer.cache`. -/
def remember (c : Composer) [Nonempty α] (init : IO α) : IO α := do
  let f ← c.topFrame
  if f.inserting then
    let v ← init
    f.group.modifyData fun d => { d with slots := d.slots.push { val := SlotVal.mk v } }
    c.advanceSlot
    return v
  else
    let gd ← f.group.data
    if h : f.slotCursor < gd.slots.size then
      c.advanceSlot
      return gd.slots[f.slotCursor].val.get!
    else
      throw <| IO.userError
        "Compose: slot underflow — remember count changed within a group \
         (wrap conditional content in withGroup)"

/-- `remember` re-initialized whenever `k` changes (`BEq`). Mirrors
`remember(key) { ... }`. -/
def rememberKeyed (c : Composer) [BEq κ] [Nonempty α] (k : κ) (init : IO α) : IO α := do
  have : Nonempty κ := ⟨k⟩
  let f ← c.topFrame
  if f.inserting then
    let v ← init
    f.group.modifyData fun d => { d with slots := d.slots.push { val := SlotVal.mk (k, v) } }
    c.advanceSlot
    return v
  else
    let gd ← f.group.data
    if h : f.slotCursor < gd.slots.size then
      let (k', v') : κ × α := gd.slots[f.slotCursor].val.get!
      c.advanceSlot
      if k' == k then
        return v'
      else
        let v ← init
        f.group.modifyData fun d =>
          { d with slots := d.slots.set! f.slotCursor { val := SlotVal.mk (k, v) } }
        return v
    else
      throw <| IO.userError
        "Compose: slot underflow — remember count changed within a group \
         (wrap conditional content in withGroup)"

/-- `rememberKeyed` with lifecycle callbacks: `onRemembered` is deferred to a
successful apply; a key change (or group removal) defers `onForgotten` of the
old value before the new value's `onRemembered`. The storage primitive behind
`DisposableEffect`. Mirrors `RememberObserver` handling in `remember`. -/
def rememberObservedKeyed (c : Composer) [BEq κ] [Nonempty α]
    (k : κ) (init : IO (α × RememberObserver)) : IO α := do
  have : Nonempty κ := ⟨k⟩
  let f ← c.topFrame
  let fresh : IO α := do
    let (v, obs) ← init
    c.pendingRemembers.modify (·.push obs.onRemembered)
    f.group.modifyData fun d =>
      { d with slots := d.slots.set! f.slotCursor { val := SlotVal.mk (k, v), observer := some obs } }
    return v
  if f.inserting then
    let (v, obs) ← init
    c.pendingRemembers.modify (·.push obs.onRemembered)
    f.group.modifyData fun d =>
      { d with slots := d.slots.push { val := SlotVal.mk (k, v), observer := some obs } }
    c.advanceSlot
    return v
  else
    let gd ← f.group.data
    if h : f.slotCursor < gd.slots.size then
      let slot := gd.slots[f.slotCursor]
      let (k', v') : κ × α := slot.val.get!
      c.advanceSlot
      if k' == k then
        return v'
      else
        if let some obs := slot.observer then
          c.pendingForgets.modify (·.push obs.onForgotten)
        fresh
    else
      throw <| IO.userError
        "Compose: slot underflow — remember count changed within a group \
         (wrap conditional content in withGroup)"

/-- Open the restartable group for `key`, creating (or fetching) its
`RecomposeScope`, refreshing the scope's captured locals, and making reads
attribute to it. Mirrors `Composer.startRestartGroup`. -/
def startRestartGroup (c : Composer) (key : UInt64) : IO RecomposeScope := do
  let g ← c.startGroup key (isNode := false)
  let gd ← g.data
  let scope ← match gd.scope with
    | some s => pure s
    | none =>
      let s ← c.freshScope g
      g.modifyData fun d => { d with scope := some s }
      pure s
  scope.locals.set (← c.locals.get)
  c.scopeStack.modify (·.push scope)
  return scope

/-- Whether the restartable body may be skipped: not inserting, the scope is
still valid, and the arguments are unchanged. When the body *will* run
(result `false`), clears the scope's read registrations (a scope observes
exactly the states its latest run reads) and re-validates it. Mirrors
`Composer.skipping` + `RecomposeScopeImpl.requiresRecompose`. -/
def shouldSkip (c : Composer) (scope : RecomposeScope) (argsChanged : Bool) : IO Bool := do
  let f ← c.topFrame
  if !f.inserting && !argsChanged && (← scope.valid.get) then
    return true
  else
    scope.reads.clear
    scope.valid.set true
    return false

/-- Advance the cursors past the current group's content without executing
it (the skip path). Mirrors `Composer.skipToGroupEnd`. -/
def skipToGroupEnd (c : Composer) : IO Unit := do
  let f ← c.topFrame
  let gd ← f.group.data
  c.modifyTopFrame fun fr =>
    { fr with childCursor := gd.children.size, slotCursor := gd.slots.size,
              nodeIndex := fr.nodeIndex + gd.nodes }

/-- Close a restartable group, storing `rerun` (the body re-invocation with
its latest arguments) on the scope for the recomposer. Mirrors
`Composer.endRestartGroup()?.updateScope`. -/
def endRestartGroup (c : Composer) (scope : RecomposeScope) (rerun : IO Unit) : IO Unit := do
  scope.rerun.set rerun
  c.scopeStack.modify (·.pop)
  c.endGroup

/-- Read observer routing state reads to the innermost active restart scope;
pushed around every composition/recomposition pass. -/
def readRouter (c : Composer) : ObservedHandle → IO Unit := fun h => do
  if let some s := (← c.scopeStack.get).back? then
    s.reads.record h

end Composer

/-- Run `body` in a group keyed by `key` — the explicit form of what the
`composable` macro injects around control-flow branches. A throw in `body`
unwinds the group (`Composer.abortTo`) and propagates. Mirrors
`Composer.startReplaceGroup`/`endReplaceGroup`. -/
def withGroup (key : UInt64) (body : Composable α) : Composable α := fun c => do
  let depth := (← c.frames.get).size
  let _ ← c.startGroup key (isNode := false)
  try
    let a ← body.run c
    c.endGroup
    return a
  catch e =>
    c.abortTo depth
    throw e

/-- Run `body` in a group keyed by (a hash of) the data key `k`: gives items
identity across reorder, so moved content keeps its state and nodes move
instead of being recreated. Mirrors `androidx.compose.runtime.key`. -/
def keyed [Hashable κ] (k : κ) (body : Composable α) : Composable α :=
  withGroup (mixKeys keyedGroupSalt (hash k)) body

/-- Positional memoization: `init` runs on first composition only; later
passes through the same slot return the stored value. State builders
(`mutableStateOf`, `derivedStateOf`) are `StateInit` and fit directly;
arbitrary `IO` initializers lift in. Mirrors
`androidx.compose.runtime.remember`. -/
def remember [Nonempty α] (init : StateInit α) : Composable α := fun c =>
  c.remember init.run

/-- `remember` that re-initializes when `k` changes. Mirrors
`remember(key1) { ... }`. -/
def rememberKeyed [BEq κ] [Nonempty α] (k : κ) (init : StateInit α) : Composable α := fun c =>
  c.rememberKeyed k init.run

/-- Emit a node into the applied tree: `create` runs once (the node is
inserted at the exact index among its siblings), `update` runs every pass
(reconcile attributes), `content` composes children beneath the node.
Mirrors `androidx.compose.runtime.ComposeNode`. -/
def emitNode (create : IO NodeVal) (update : NodeVal → Composable Unit)
    (content : Composable Unit) : Composable Unit := fun c => do
  let depth := (← c.frames.get).size
  -- The insertion index is the parent frame's cursor position, read before
  -- the node group's own frame is pushed.
  let parentIdx := (← c.topFrame).nodeIndex
  let g ← c.startGroup nodeGroupKey (isNode := true)
  try
    let gd ← g.data
    let node ← match gd.node with
      | some n => pure n
      | none => do
        let n ← create
        c.applier.insert (← c.currentNodeParent) parentIdx n
        -- Record node and count at insert time (not `endGroup`) so a throw
        -- in `content` cannot leave a node the group tree does not count.
        g.modifyData fun d => { d with node := some n, nodes := 1 }
        pure n
    c.nodeParents.modify (·.push node)
    try
      update node |>.run c
      content.run c
      c.endGroup
    finally
      c.nodeParents.modify (·.pop)
  catch e =>
    c.abortTo depth
    throw e

/-- Composable-level `Composer.startRestartGroup`; with `shouldSkip`,
`skipToGroupEnd` and `endRestartGroup` this is the exact surface the
`composable` macro (M2) targets. -/
def startRestartGroup (key : UInt64) : Composable RecomposeScope := fun c =>
  c.startRestartGroup key

/-- Composable-level `Composer.shouldSkip`; see there. -/
def shouldSkip (scope : RecomposeScope) (argsChanged : Bool) : Composable Bool := fun c =>
  c.shouldSkip scope argsChanged

/-- Composable-level `Composer.skipToGroupEnd`; see there. -/
def skipToGroupEnd : Composable Unit := fun c =>
  c.skipToGroupEnd

/-- Composable-level `Composer.endRestartGroup`: stores `rerun` — the whole
restartable function applied to its latest arguments — on the scope. -/
def endRestartGroup (scope : RecomposeScope) (rerun : Composable Unit) : Composable Unit := fun c =>
  c.endRestartGroup scope (rerun.run c)

end Compose
