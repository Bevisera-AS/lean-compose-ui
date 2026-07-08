import Compose
import Std.Data.HashMap

/-!
# TestApplier

A labeled mutable tree driven through `Compose.Applier` for the runtime test
suites: logs every applier operation and renders the tree as an s-expression
so tests can assert exact shapes and event sequences. Nodes are ids into a
side store (labels/children maps), sidestepping the recursive-`IO.Ref` knot a
direct node structure would need.
-/

namespace Tests
open Compose

/-- Move `count` elements of `xs` from `src` to `dst` (both indices in the
pre-move list), Compose's `AbstractApplier.move` convention. -/
def moveRange (xs : Array α) (src dst count : Nat) : Array α :=
  if src == dst || count == 0 then xs else
    let dest := if src > dst then dst else dst - count
    let block := xs.extract src (src + count)
    let rest := xs.extract 0 src ++ xs.extract (src + count) xs.size
    rest.extract 0 dest ++ block ++ rest.extract dest rest.size

#guard moveRange #[1, 2, 3, 4, 5] 2 0 2 == #[3, 4, 1, 2, 5]
#guard moveRange #[1, 2, 3, 4, 5] 0 3 1 == #[2, 3, 1, 4, 5]
#guard moveRange #[1, 2, 3, 4, 5] 1 1 2 == #[1, 2, 3, 4, 5]
#guard moveRange #[1, 2, 3] 2 0 1 == #[3, 1, 2]

/-- Remove `count` elements of `xs` starting at `idx`. -/
def removeRange (xs : Array α) (idx count : Nat) : Array α :=
  xs.extract 0 idx ++ xs.extract (idx + count) xs.size

#guard removeRange #[1, 2, 3, 4] 1 2 == #[1, 4]
#guard removeRange #[1, 2, 3] 0 3 == (#[] : Array Nat)

/-- A node of the test tree (id into the `TestTree` store). -/
structure TestNode where
  id : Nat
  deriving BEq, Repr, Inhabited

/-- Store backing the test nodes: labels, child lists, and an operation log. -/
structure TestTree where
  nextId : IO.Ref Nat
  labels : IO.Ref (Std.HashMap Nat String)
  kids : IO.Ref (Std.HashMap Nat (Array Nat))
  log : IO.Ref (Array String)

namespace TestTree

/-- Fresh tree containing just the root node (id 0, label "root"). -/
def create : IO TestTree :=
  return { nextId := ← IO.mkRef 1
           labels := ← IO.mkRef (Std.HashMap.emptyWithCapacity.insert 0 "root")
           kids := ← IO.mkRef (Std.HashMap.emptyWithCapacity.insert 0 #[])
           log := ← IO.mkRef #[] }

/-- Allocate a node with the given label. -/
def newNode (t : TestTree) (label : String) : IO TestNode := do
  let id ← t.nextId.modifyGet fun n => (n, n + 1)
  t.labels.modify (·.insert id label)
  t.kids.modify (·.insert id #[])
  return ⟨id⟩

def labelOf (t : TestTree) (n : TestNode) : IO String :=
  return (← t.labels.get).getD n.id "?"

def setLabel (t : TestTree) (n : TestNode) (label : String) : IO Unit :=
  t.labels.modify (·.insert n.id label)

/-- Drain the operation log. -/
def takeLog (t : TestTree) : IO (Array String) :=
  t.log.modifyGet fun l => (l, #[])

/-- The `Applier` over test nodes; every operation is logged. -/
def applier (t : TestTree) : Applier TestNode where
  root := ⟨0⟩
  insert p i ch := do
    t.log.modify (·.push s!"insert {← t.labelOf ch} at {i} in {← t.labelOf p}")
    t.kids.modify fun m => m.insert p.id ((m.getD p.id #[]).insertIdx! i ch.id)
  remove p i n := do
    t.log.modify (·.push s!"remove {n} at {i} in {← t.labelOf p}")
    t.kids.modify fun m => m.insert p.id (removeRange (m.getD p.id #[]) i n)
  move p src dst n := do
    t.log.modify (·.push s!"move {n} from {src} to {dst} in {← t.labelOf p}")
    t.kids.modify fun m => m.insert p.id (moveRange (m.getD p.id #[]) src dst n)
  onClear := do
    t.log.modify (·.push "clear")
    t.kids.modify fun m => m.insert 0 #[]

private partial def renderNode (t : TestTree) (id : Nat) : IO String := do
  let label := (← t.labels.get).getD id "?"
  let kids := (← t.kids.get).getD id #[]
  if kids.isEmpty then
    return label
  else
    let parts ← kids.mapM (t.renderNode ·)
    return s!"({label} {" ".intercalate parts.toList})"

/-- Render the whole tree as an s-expression, e.g. `(root a (box x y) b)`. -/
def render (t : TestTree) : IO String := t.renderNode 0

end TestTree

/-- Emit a leaf node labeled `label` (`create`-time label, never updated). -/
def emitLabeled (t : TestTree) (label : String) (content : Composable Unit := pure ()) :
    Composable Unit :=
  emitNode (return .mk (← t.newNode label)) (fun _ => pure ()) content

/-- Emit a node whose label is reconciled in the update phase every pass. -/
def emitText (t : TestTree) (label : String) : Composable Unit :=
  emitNode (return .mk (← t.newNode label))
    (fun n => fun _ => t.setLabel n.get! label)
    (pure ())

/-- Explicit-combinator restartable function: exactly the shape the M2
`composable` macro will generate (no arguments, hence `argsChanged := false`). -/
partial def restartable (key : UInt64) (body : Composable Unit) : Composable Unit := fun c => do
  let scope ← c.startRestartGroup key
  if ← c.shouldSkip scope (argsChanged := false) then
    c.skipToGroupEnd
  else
    body.run c
  c.endRestartGroup scope ((restartable key body).run c)

end Tests
