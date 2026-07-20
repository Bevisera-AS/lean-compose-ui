module

public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer

public section

namespace Compose

/-!
# Recomposer and Composition

State writes invalidate `RecomposeScope`s and enqueue them on the composer;
`Recomposer.drainRecompositions` processes the queue in tree order (parents
first), skipping scopes an ancestor already re-ran, until quiescent — bounded
by an iteration cap with a loud error, like Compose. Deferred lifecycle
callbacks dispatch only after the whole drain applies successfully.

`Composition` is the public entry point: create over an applier, set content,
dispose. Mirrors `androidx.compose.runtime.Recomposer`/`Composition`.

**Exception safety.** A throw inside composable content propagates to the
caller (`Composition.create`/`setContent`/`drain`) and never corrupts the
runtime: open groups unwind (`Composer.abortTo`, which also refreshes the
aborted spine's node counts to the applier's live contents), so the applier
and the group tree agree; in-place slot replacements (`rememberObservedKeyed`
key changes) are undone — the previous observer restored, its queued forget
retracted, the enclosing scope re-invalidated — so a retry re-runs the
replacement exactly once (`Composer.rollbackSlotReplacements`); remembers/
side effects queued by the failed pass are abandoned, while already-collected
forgets (whose removals did apply) stay queued for the next successful apply;
a failed *initial* composition rolls back to a clean slate (`composed` stays
false, retry composes from scratch); a failed re-run leaves its scope invalid
and queued — and re-queues every drained-but-not-yet-re-run scope of the same
batch — so a later drain retries once the offending state changes; a `create`
whose initial pass applied but whose trailing drain threw disposes itself
before propagating (the caller never gets a handle). (Compose's `onAbandoned`
protocol is not modeled: a `DisposableEffect` whose pass never applied simply
never runs either end.)
-/

/-- Drives recomposition for one composition. Mirrors
`androidx.compose.runtime.Recomposer` (single-threaded: the app loop calls
`drainRecompositions` once per frame). -/
structure Recomposer where
  composer : Composer

namespace Recomposer

/-- Iteration cap for one drain: recomposition that keeps invalidating itself
past this many passes is reported as an error (Compose's re-composition
attempt limit). -/
def maxIterations : Nat := 100

/-- Index of `gid` in `p`'s children. -/
private def childIdx (p : Group) (gid : Nat) : IO (Option Nat) := do
  let pd ← p.data
  for j in [0 : pd.children.size] do
    if (← pd.children[j]!.data).gid == gid then
      return some j
  return none

/-- Path of child indices from the root down to `g` (tree order key). -/
private partial def groupPath (g : Group) (acc : List Nat := []) : IO (List Nat) := do
  match (← g.data).parent with
  | none => return acc
  | some p =>
    let some idx ← childIdx p (← g.data).gid
      | throw <| IO.userError "Compose: group missing from its parent's children (corrupt group tree)"
    groupPath p (idx :: acc)

/-- Base applier index and node parent for composing at `g`: walks up the
group tree summing the node counts of preceding siblings until the nearest
node group (or the applier root). -/
private partial def locate (c : Composer) (g : Group) (acc : Nat := 0) :
    IO (Nat × NodeVal) := do
  match (← g.data).parent with
  | none => return (acc, c.applier.root)
  | some p =>
    let pd ← p.data
    let some idx ← childIdx p (← g.data).gid
      | throw <| IO.userError "Compose: group missing from its parent's children (corrupt group tree)"
    let mut acc' := acc
    for j in [0 : idx] do
      acc' := acc' + (← pd.children[j]!.data).nodes
    if pd.isNode then
      if let some n := pd.node then
        return (acc', n)
      else
        throw <| IO.userError "Compose: node group without a node"
    else
      locate c p acc'

/-- Re-run one invalidated scope in place: position the composer's cursors at
the scope's group (correct base node index, node parent, captured locals) and
invoke the stored rerun closure. No-ops for disposed scopes and for scopes an
ancestor's re-run already validated. -/
def rerunScope (r : Recomposer) (s : RecomposeScope) : IO Unit := do
  if ← s.disposed.get then return
  if ← s.valid.get then return
  let c := r.composer
  let (base, np) ← locate c s.group
  c.frames.set #[]
  c.nodeParents.set #[np]
  c.scopeStack.set #[]
  c.locals.set (← s.locals.get)
  c.pendingEnter.set (some (s.group, base))
  c.standaloneRerun.set true
  let remembersMark ← c.pendingRemembers.get
  let effectsMark ← c.pendingSideEffects.get
  let replacementsMark := (← c.slotReplacements.get).size
  try
    (← s.rerun.get)
    c.commitSlotReplacements replacementsMark
  catch e =>
    -- Failed re-run: unwind to a consistent tree (refreshing the aborted
    -- spine's node counts), patch the scope's ancestors with the delta of
    -- the pass's surviving applier changes, undo in-place slot
    -- replacements, abandon this pass's remembers/side effects (their slots
    -- never applied; collected forgets stay — those removals did apply),
    -- and leave the scope invalid and queued so a later drain retries once
    -- the offending state changes.
    let preAbortNodes := (← s.group.data).nodes
    c.abortTo 0
    Composer.propagateNodeDelta s.group preAbortNodes (← s.group.data).nodes
    c.pendingEnter.set none
    c.rollbackSlotReplacements replacementsMark
    c.pendingRemembers.set remembersMark
    c.pendingSideEffects.set effectsMark
    s.valid.set false
    c.invalidations.modify fun q => if q.any (·.id == s.id) then q else q.push s
    throw e
  finally c.standaloneRerun.set false

private partial def drainLoop (r : Recomposer) (fuel : Nat) : IO Unit := do
  let pending ← r.composer.invalidations.modifyGet fun q => (q, #[])
  let mut live := #[]
  for s in pending do
    unless (← s.disposed.get) || (← s.valid.get) do
      live := live.push (← groupPath s.group, s)
  if live.isEmpty then return
  if fuel == 0 then
    throw <| IO.userError <|
      s!"Compose: recomposition did not settle after {maxIterations} iterations — " ++
      "likely an invalidation loop (state a scope reads is written unconditionally " ++
      "during its recomposition)"
  -- Tree order: parents before descendants, document order among siblings.
  let sorted := live.qsort fun a b => decide (a.1 < b.1)
  let mut idx := 0
  for (_, s) in sorted do
    try
      r.rerunScope s
    catch e =>
      -- One scope's throw must not strand the rest of the batch: everything
      -- drained but not yet re-run goes back on the queue (still invalid),
      -- then the error propagates (`rerunScope` re-queued the thrower).
      for (_, rest) in sorted.extract (idx + 1) sorted.size do
        unless (← rest.disposed.get) || (← rest.valid.get) do
          r.composer.invalidations.modify fun q =>
            if q.any (·.id == rest.id) then q else q.push rest
      throw e
    idx := idx + 1
  drainLoop r (fuel - 1)

/-- Drain the invalidation queue until quiescent: scopes re-run in tree order
(a scope already re-run by an ancestor this drain is skipped via its `valid`
flag); invalidations raised during recomposition join the same drain, bounded
by `maxIterations`. On success, dispatches the deferred lifecycle events
(forgotten → remembered → side effects). -/
def drainRecompositions (r : Recomposer) : IO Unit := do
  withReadObserver r.composer.readRouter (drainLoop r maxIterations)
  r.composer.dispatchEffects

end Recomposer

/-- A root composition binding a `Composable` content tree to an applier.
Mirrors `androidx.compose.runtime.Composition`. -/
structure Composition where
  composer : Composer
  recomposer : Recomposer
  content : IO.Ref (Composable Unit)
  disposed : IO.Ref Bool
  /-- Whether the initial composition ran (the first pass composes the root
  group in inserting mode; later passes match). -/
  composed : IO.Ref Bool

namespace Composition

/-- (Re)compose from the root group, matching against the existing tree, then
drain any invalidations raised while composing. `composed` flips only after a
successful initial pass; a throw rolls that pass fully back (see the module
docstring for the exception contract). -/
private def composeRoot (comp : Composition) : IO Unit := do
  let c := comp.composer
  let inserting := !(← comp.composed.get)
  c.frames.set #[{ group := c.rootGroup, inserting }]
  c.nodeParents.set #[c.applier.root]
  c.scopeStack.set #[]
  c.locals.set .empty
  c.pendingEnter.set none
  c.standaloneRerun.set false
  let remembersMark ← c.pendingRemembers.get
  let effectsMark ← c.pendingSideEffects.get
  let replacementsMark := (← c.slotReplacements.get).size
  try
    withReadObserver c.readRouter do
      (← comp.content.get).run c
      c.endGroup
    c.commitSlotReplacements replacementsMark
    comp.composed.set true
  catch e =>
    c.abortTo 0
    if inserting then
      -- Failed initial pass: nothing was applied — drop everything it
      -- queued so the retry composes from a clean slate.
      c.pendingForgets.set #[]
      c.pendingRemembers.set #[]
      c.pendingSideEffects.set #[]
      c.slotReplacements.set #[]
      c.invalidations.set #[]
    else
      c.rollbackSlotReplacements replacementsMark
      c.pendingRemembers.set remembersMark
      c.pendingSideEffects.set effectsMark
    throw e
  comp.recomposer.drainRecompositions

/-- Tear down the composition: every remembered observer is forgotten
(depth-first), the whole group tree is severed (`severSubtree` — reference
cycles broken so RC can free it), the applier is cleared, further
recompositions are inert. Mirrors `Composition.dispose`. -/
def dispose (comp : Composition) : IO Unit := do
  if ← comp.disposed.get then return
  comp.disposed.set true
  let c := comp.composer
  c.collectDisposals c.rootGroup
  severSubtree c.rootGroup
  c.invalidations.set #[]
  c.applier.onClear
  c.dispatchEffects

/-- Create a composition over `applier` and compose `content` into it
(including the initial effect dispatch). Mirrors
`androidx.compose.runtime.Composition(applier, parent)` + `setContent`. -/
def create [Nonempty N] (applier : Applier N) (content : Composable Unit) :
    IO Composition := do
  let composer ← Composer.create applier.erase
  let comp : Composition :=
    { composer, recomposer := ⟨composer⟩
      content := ← IO.mkRef content
      disposed := ← IO.mkRef false
      composed := ← IO.mkRef false }
  try
    comp.composeRoot
  catch e =>
    -- The initial pass applied but the trailing drain threw: the caller
    -- never gets a handle, so dispose here or the applied nodes and queued
    -- observers leak. (A failed initial *pass* already rolled back to a
    -- clean slate — nothing to dispose.) The failed drain's un-dispatched
    -- remembers/side effects are abandoned (`onAbandoned` is not modeled).
    if ← comp.composed.get then
      composer.pendingRemembers.set #[]
      composer.pendingSideEffects.set #[]
      comp.dispose
    throw e
  return comp

/-- Replace the composition's content and recompose from the root (existing
groups are matched and reused). Mirrors `Composition.setContent`. -/
def setContent (comp : Composition) (content : Composable Unit) : IO Unit := do
  comp.content.set content
  comp.composeRoot

/-- Convenience for the app loop and tests: drain pending invalidations. -/
def drain (comp : Composition) : IO Unit :=
  comp.recomposer.drainRecompositions

/-- Install the invalidation observer: `f` runs whenever a scope of this
composition is invalidated. The M5 app shell points this at the window's
needs-frame flag (Compose's `Recomposer` waking its apply loop on
`invalidate`). -/
def setOnInvalidate (comp : Composition) (f : IO Unit) : IO Unit :=
  comp.composer.onInvalidate.set f

end Composition

end Compose

end
