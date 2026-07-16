module

public import Compose.Ui.Input.HitTest
public meta import Compose.Ui.Input.HitTest

public section

namespace Compose.Test

/-!
# Semantics tree (`Compose/Test/Semantics.lean`)

Builds the tree of semantics nodes the MT test framework's finders search: a
walk over the live `LayoutNode` tree collecting every node whose modifier
chain carries semantics (`Modifier.semanticsProps`), with bounds resolved to
root (render-px) coordinates from the real layout. Overlay layers (popups,
dialogs) are ordinary children of the window root, so one walk covers them.

Two views, mirroring `androidx.compose.ui.test`'s merged/unmerged trees:

* **raw** (unmerged): every semantics-bearing node appears.
* **merged** (the default): a node with `mergeDescendants` (every
  `Modifier.clickable`) absorbs the *texts* of its non-merging descendants
  and hides them — so `Button onClick (Text "OK")` is one node with
  `texts = #["OK"]` and `role = button`. Nested merging nodes stay separate
  children (Compose's merge boundary rule). Only text merges; other
  properties stay with the node that stated them — a documented
  simplification that covers what finders and assertions actually need.
-/

/-- One node of the semantics tree. `layout` is the live `LayoutNode` it was
collected from (focus assertions compare against it); `texts` is the node's
own text plus, in the merged tree, the texts absorbed from descendants.
Mirrors `androidx.compose.ui.semantics.SemanticsNode`. -/
structure SemanticsNode where
  /-- The layout node carrying the semantics chain. -/
  layout : LayoutNode
  /-- The chain's combined properties (`Modifier.semanticsProps`). -/
  props : SemanticsProps
  /-- Own `text` plus merged descendant texts, in tree order. -/
  texts : Array String
  /-- Outer-box bounds in root (render-px) coordinates. -/
  bounds : Rect
  /-- Semantics children (transparent layout nodes are skipped over). -/
  children : Array SemanticsNode

instance : Inhabited SemanticsNode :=
  ⟨{ layout := default, props := {}, texts := #[], bounds := .zero, children := #[] }⟩

/-- Collect the semantics forest of the subtree at `n` (whose outer box
starts at `origin` in root coordinates): nodes without semantics contribute
their descendants transparently. -/
partial def collectSemantics (n : LayoutNode) (origin : Offset := .zero) :
    IO (Array SemanticsNode) := do
  let d ← n.data
  let contentOrigin := origin + d.contentOffset.toOffset
  let mut kids : Array SemanticsNode := #[]
  for ch in d.children do
    kids := kids ++ (← collectSemantics ch (contentOrigin + (← ch.data).position.toOffset))
  match d.modifier.semanticsProps with
  | some props =>
    return #[{ layout := n, props
               texts := match props.text with | some t => #[t] | none => #[]
               bounds := .ofOffsetSize origin d.size.toSize
               children := kids }]
  | none => return kids

namespace SemanticsNode

mutual

/-- The merged view of this node (see the module docstring): a
`mergeDescendants` node absorbs the texts of its non-merging descendants;
nested merging nodes remain as children. -/
partial def merged (n : SemanticsNode) : SemanticsNode :=
  if n.props.mergeDescendants then
    let (texts, keep) := absorb n.children
    { n with texts := n.texts ++ texts, children := keep }
  else
    { n with children := n.children.map merged }

/-- Fold a merged node's descendant forest: texts of non-merging nodes (and
their subtrees) are absorbed; merging nodes survive, themselves merged. -/
private partial def absorb (cs : Array SemanticsNode) :
    Array String × Array SemanticsNode := Id.run do
  let mut texts : Array String := #[]
  let mut keep : Array SemanticsNode := #[]
  for c in cs do
    if c.props.mergeDescendants then
      keep := keep.push c.merged
    else
      texts := texts ++ c.texts
      let (t, k) := absorb c.children
      texts := texts ++ t
      keep := keep ++ k
  return (texts, keep)

end

/-- The subtree flattened in preorder (what finders filter). -/
partial def flatten (n : SemanticsNode) : Array SemanticsNode :=
  n.children.foldl (fun acc c => acc ++ c.flatten) #[n]

/-- One-line description: integer bounds, then the stated properties with
the (possibly merged) `texts` shown as a list. -/
def describe (n : SemanticsNode) : String :=
  let b := n.bounds
  let boundsPart :=
    s!"({b.left.toInt32},{b.top.toInt32} {(b.right - b.left).toInt32}×{(b.bottom - b.top).toInt32})"
  let propsPart := SemanticsProps.describe { n.props with text := none }
  let textsPart :=
    if n.texts.isEmpty then ""
    else " texts=[" ++ ", ".intercalate (n.texts.toList.map (s!"\"{·}\"")) ++ "]"
  boundsPart ++ (if propsPart.isEmpty then "" else " " ++ propsPart) ++ textsPart

/-- Indented dump lines of the subtree. -/
partial def dumpLines (n : SemanticsNode) (indent : Nat := 0) : Array String :=
  let pad := String.ofList (List.replicate (indent * 2) ' ')
  n.children.foldl (fun acc c => acc ++ c.dumpLines (indent + 1))
    #[s!"{pad}- {n.describe}"]

end SemanticsNode

/-- The window's semantics forest: walk the layout tree from `root` and, by
default, merge (`SemanticsNode.merged`). Call after a render so layout
positions are current. -/
def semanticsForest (root : LayoutNode) (merged : Bool := true) :
    IO (Array SemanticsNode) := do
  let raw ← collectSemantics root
  return if merged then raw.map (·.merged) else raw

/-- Render a forest as an indented dump — appended to every finder/assertion
failure, where it is worth its weight in gold. -/
def dumpForest (forest : Array SemanticsNode) : String :=
  if forest.isEmpty then "  (empty semantics tree)"
  else "\n".intercalate (forest.foldl (fun acc n => acc ++ n.dumpLines 1) #[]).toList

end Compose.Test

end
