import Compose.Runtime.Composer

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
    let idx := (← childIdx p (← g.data).gid).getD 0
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
    let idx := (← childIdx p (← g.data).gid).getD 0
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
  try (← s.rerun.get)
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
  for (_, s) in sorted do
    r.rerunScope s
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

namespace Composition

/-- (Re)compose from the root group, matching against the existing tree, then
drain any invalidations raised while composing. -/
private def composeRoot (comp : Composition) : IO Unit := do
  let c := comp.composer
  c.frames.set #[{ group := c.rootGroup }]
  c.nodeParents.set #[c.applier.root]
  c.scopeStack.set #[]
  c.locals.set .empty
  c.pendingEnter.set none
  c.standaloneRerun.set false
  withReadObserver c.readRouter do
    (← comp.content.get).run c
    c.endGroup
  comp.recomposer.drainRecompositions

/-- Create a composition over `applier` and compose `content` into it
(including the initial effect dispatch). Mirrors
`androidx.compose.runtime.Composition(applier, parent)` + `setContent`. -/
def create [Nonempty N] (applier : Applier N) (content : Composable Unit) :
    IO Composition := do
  let composer ← Composer.create applier.erase
  let comp : Composition :=
    { composer, recomposer := ⟨composer⟩
      content := ← IO.mkRef content
      disposed := ← IO.mkRef false }
  comp.composeRoot
  return comp

/-- Replace the composition's content and recompose from the root (existing
groups are matched and reused). Mirrors `Composition.setContent`. -/
def setContent (comp : Composition) (content : Composable Unit) : IO Unit := do
  comp.content.set content
  comp.composeRoot

/-- Convenience for the app loop and tests: drain pending invalidations. -/
def drain (comp : Composition) : IO Unit :=
  comp.recomposer.drainRecompositions

/-- Tear down the composition: every remembered observer is forgotten
(depth-first), the applier is cleared, further recompositions are inert.
Mirrors `Composition.dispose`. -/
def dispose (comp : Composition) : IO Unit := do
  if ← comp.disposed.get then return
  comp.disposed.set true
  let c := comp.composer
  c.collectDisposals c.rootGroup
  c.rootGroup.modifyData fun d => { d with children := #[], slots := #[], nodes := 0 }
  c.applier.onClear
  c.dispatchEffects

end Composition

end Compose
