module

public import Compose.Ui.Input.HitTest
public meta import Compose.Ui.Input.HitTest

public section

namespace Compose

/-!
# Focus (`Compose/Ui/Input/Focus.lean`)

Per-window focus tracking, mirroring `androidx.compose.ui.focus.FocusManager`
(one per `WindowContext`; the input router owns it):

* `Modifier.focusable` marks focus targets; a chain is a target iff it has a
  `focusable` element and none is disabled (`Modifier.focusEnabled`).
* **Traversal** is layout order: tree preorder over the focusable nodes
  (Tab = next, Shift-Tab = previous, both wrapping) — DESIGN.md's simplified
  one-dimensional order, not Compose's 2D `FocusDirection` search.
* **Click-to-focus**: on a press, the deepest focusable on the hit path gains
  focus; a press hitting no focusable clears focus (the router calls
  `focusOnPress`). Esc clears (router fallback).
* **Key routing** (`dispatchKey`): the focused node's `Modifier.onKeyEvent`
  handlers run first (innermost first), then its ancestors' bottom-up; a
  handler returning `true` consumes. App-level fallbacks (Tab traversal, Esc)
  run only when nothing consumed. `dispatchTextInput` routes committed text
  the same way through `Modifier.onTextInput`.

Focus changes run every `Modifier.onFocusChanged` handler on the outgoing
node (with `false`) before the incoming node's (with `true`), then the
manager's `onFocusTarget` hook (the router uses it for the M11 IME toggle —
see `Compose.Ui.Input.Keyboard`).
-/

/-- Per-window focus state. Create one per `WindowContext` via
`FocusManager.create` (the input router does). Mirrors
`androidx.compose.ui.focus.FocusManager` + the owner's focus tracking. -/
structure FocusManager where
  /-- The tree whose focusables are traversed. -/
  root : LayoutNode
  /-- The currently focused node. -/
  focusedRef : IO.Ref (Option LayoutNode)
  /-- Focus saved when each modal scope opened, `(scope id, prior focus)`, to
  restore when that scope closes (`pushModalScope`/`popModalScope`). -/
  savedFocus : IO.Ref (Array (Nat × Option LayoutNode))
  /-- Runs after every focus change with the new target (`none` = cleared).
  The router hooks the M11 text-input lifecycle here. -/
  onFocusTarget : Option LayoutNode → IO Unit

namespace FocusManager

/-- Fresh manager focused on nothing. -/
def create (root : LayoutNode) (onFocusTarget : Option LayoutNode → IO Unit := fun _ => pure ()) :
    IO FocusManager :=
  return { root, focusedRef := ← IO.mkRef none, savedFocus := ← IO.mkRef #[], onFocusTarget }

/-- The focused node, if any. -/
def focused (fm : FocusManager) : IO (Option LayoutNode) := fm.focusedRef.get

/-- Whether `n` is the focused node (by node identity). -/
def isFocused (fm : FocusManager) (n : LayoutNode) : IO Bool := do
  match ← fm.focusedRef.get with
  | some f => return (← f.nodeId) == (← n.nodeId)
  | none => return false

/-- Run every `onFocusChanged` handler on `n`'s chain with `hasFocus`. -/
private def notify (n : LayoutNode) (hasFocus : Bool) : IO Unit := do
  for e in (← n.data).modifier.elems do
    if let .focus (.onFocusChanged h) := e then h hasFocus

/-- Move focus to `target` (`none` clears): no-op when unchanged, otherwise
notifies the outgoing node (`false`) before the incoming one (`true`), then
the `onFocusTarget` hook. Mirrors `FocusRequester.requestFocus` /
`FocusManager.clearFocus`. -/
def requestFocus (fm : FocusManager) (target : Option LayoutNode) : IO Unit := do
  let old ← fm.focusedRef.get
  let oldId ← old.mapM (·.nodeId)
  let newId ← target.mapM (·.nodeId)
  if oldId == newId then return
  fm.focusedRef.set target
  if let some o := old then notify o false
  if let some t := target then notify t true
  fm.onFocusTarget target

/-- Clear focus. Mirrors `FocusManager.clearFocus`. -/
def clearFocus (fm : FocusManager) : IO Unit := fm.requestFocus none

/-- Whether `n` is still in the manager's tree (its parent chain reaches the
root — false once `severParentLinks` detached it). -/
def isAttached (fm : FocusManager) (n : LayoutNode) : IO Bool :=
  n.isDescendantOf fm.root

/-- A subtree is about to be detached (the applier's detach hook, parent
links still intact): when the focused node is inside it, clear focus through
the normal path, so `onFocusChanged false` and `onFocusTarget` (the IME stop)
fire — removal behaves like a click-away, and key/text routing never reaches
a dead node. -/
def clearIfDetaching (fm : FocusManager) (subtree : LayoutNode) : IO Unit := do
  if let some f ← fm.focusedRef.get then
    if ← f.isDescendantOf subtree then fm.clearFocus

/-- The subtree root of the topmost open modal scope (`Modifier.focusScope` —
the last such node in preorder, since overlay layers compose after the main
content), or `none` when no modal is open. -/
partial def topModalScope (fm : FocusManager) : IO (Option LayoutNode) := do
  go fm.root none
where
  go (n : LayoutNode) (acc : Option LayoutNode) : IO (Option LayoutNode) := do
    let d ← n.data
    let acc := if d.modifier.focusScopeId.isSome then some n else acc
    d.children.foldlM (fun acc ch => go ch acc) acc

/-- The focus targets in preorder (layout order) — the Tab traversal sequence.
When a modal scope is open, traversal is confined to its subtree, so
focusables underneath the scrim are skipped. -/
partial def focusables (fm : FocusManager) : IO (Array LayoutNode) := do
  let start ← match ← fm.topModalScope with
    | some scope => pure scope
    | none => pure fm.root
  go start #[]
where
  go (n : LayoutNode) (acc : Array LayoutNode) : IO (Array LayoutNode) := do
    let d ← n.data
    let acc := if d.modifier.focusEnabled then acc.push n else acc
    d.children.foldlM (fun acc ch => go ch acc) acc

/-- Move focus to the next (or, `backward`, previous) focusable in layout
order, wrapping at the ends; from no focus, Tab lands on the first and
Shift-Tab on the last. Mirrors `FocusManager.moveFocus(Next/Previous)`. -/
def moveFocus (fm : FocusManager) (backward : Bool := false) : IO Unit := do
  let fs ← fm.focusables
  if fs.isEmpty then return
  let curId ← (← fm.focusedRef.get).mapM (·.nodeId)
  let mut curIdx : Option Nat := none
  for h : i in [0:fs.size] do
    if (some (← fs[i].nodeId)) == curId then curIdx := some i
  let next := match curIdx with
    | none => if backward then fs.size - 1 else 0
    | some i => if backward then (i + fs.size - 1) % fs.size else (i + 1) % fs.size
  fm.requestFocus (some fs[next]!)

/-- Click-to-focus on a press: focus the deepest focusable node on the hit
path, or clear when the press hit none. -/
def focusOnPress (fm : FocusManager) (path : Array HitTarget) : IO Unit := do
  for i in [0:path.size] do
    let t := path[path.size - 1 - i]!
    if (← t.node.data).modifier.focusEnabled then
      fm.requestFocus (some t.node)
      return
  fm.clearFocus

/-- A modal overlay opened: save the current focus (to restore on close) and
clear it, so nothing under the scrim stays focused and Tab starts fresh inside
the modal (traversal is scoped by `focusables`). -/
def pushModalScope (fm : FocusManager) (id : Nat) : IO Unit := do
  fm.savedFocus.modify (·.push (id, ← fm.focusedRef.get))
  fm.clearFocus

/-- The modal overlay `id` closed: restore the focus saved when it opened (if
that node was focused before) — unless that node has since left the tree, in
which case focus is cleared instead of resurrecting it. -/
def popModalScope (fm : FocusManager) (id : Nat) : IO Unit := do
  let st ← fm.savedFocus.get
  let saved := (st.find? (·.1 == id)).bind (·.2)
  fm.savedFocus.set (st.filter (·.1 != id))
  if let some n := saved then
    if ← fm.isAttached n then fm.requestFocus (some n) else fm.clearFocus

/-- Route a key event: the focused node's `onKeyEvent` handlers first
(innermost first), then its ancestors' bottom-up; `true` = consumed. `false`
when nothing is focused or nothing consumed (app fallbacks may then act). -/
partial def dispatchKey (fm : FocusManager) (ke : KeyEvent) : IO Bool := do
  match ← fm.focusedRef.get with
  | none => return false
  | some n => up n
where
  /-- Run `n`'s handlers innermost-first, then recurse to the parent. -/
  up (n : LayoutNode) : IO Bool := do
    let d ← n.data
    for i in [0:d.modifier.elems.size] do
      if let some (.focus (.onKeyEvent h)) := d.modifier.elems[d.modifier.elems.size - 1 - i]? then
        if ← h ke then return true
    match d.parent with
    | some p => up p
    | none => return false

/-- Route committed text input to the focused node's `onTextInput` handlers
(innermost first, then ancestors); `true` = consumed. -/
partial def dispatchTextInput (fm : FocusManager) (text : String) : IO Bool := do
  match ← fm.focusedRef.get with
  | none => return false
  | some n => up n
where
  up (n : LayoutNode) : IO Bool := do
    let d ← n.data
    for i in [0:d.modifier.elems.size] do
      if let some (.focus (.onTextInput h)) := d.modifier.elems[d.modifier.elems.size - 1 - i]? then
        if ← h text then return true
    match d.parent with
    | some p => up p
    | none => return false

/-- Route an IME composition (`textEditing`) update to the focused node's
`onTextEditing` handlers (innermost first, then ancestors); `true` =
consumed. M11 addition, mirroring `dispatchTextInput`. -/
partial def dispatchTextEditing (fm : FocusManager) (text : String)
    (start length : Int32) : IO Bool := do
  match ← fm.focusedRef.get with
  | none => return false
  | some n => up n
where
  up (n : LayoutNode) : IO Bool := do
    let d ← n.data
    for i in [0:d.modifier.elems.size] do
      if let some (.focus (.onTextEditing h)) := d.modifier.elems[d.modifier.elems.size - 1 - i]? then
        if ← h text start length then return true
    match d.parent with
    | some p => up p
    | none => return false

/-- The node whose chain carries `Modifier.focusRequester` with id `rid`, if
any (tree preorder; the first match wins). -/
partial def findRequester (fm : FocusManager) (rid : UInt64) :
    IO (Option LayoutNode) :=
  go fm.root
where
  go (n : LayoutNode) : IO (Option LayoutNode) := do
    let d ← n.data
    let mine := d.modifier.elems.any fun e =>
      match e with
      | .focus (.requester i) => i == rid
      | _ => false
    if mine then return some n
    for ch in d.children do
      if let some hit ← go ch then return some hit
    return none

end FocusManager

/-! ## Programmatic focus requests (M14b) -/

/-- A handle for moving focus programmatically: create one in composition
with `rememberFocusRequester`, attach it to a focusable node via
`Modifier.focusRequester` (alongside `Modifier.focusable`), and call
`requestFocus` from handlers or effects. Mirrors
`androidx.compose.ui.focus.FocusRequester`. -/
structure FocusRequester where
  /-- Identity linking the handle to its `Modifier.focusRequester` element. -/
  id : UInt64
  /-- The window's focus manager, installed by the input pipeline (shared
  cell — re-installing input rebinds every requester). -/
  manager : IO.Ref (Option FocusManager)

instance : Nonempty FocusRequester :=
  ⟨{ id := 0, manager := Classical.choice inferInstance }⟩

/-- Move focus to the node this requester is attached to. Throws a clear
misuse error when the requester was never attached (`Modifier.focusRequester`
missing), the node is not focusable, or no input pipeline is installed.
Mirrors `FocusRequester.requestFocus`. -/
def FocusRequester.requestFocus (r : FocusRequester) : IO Unit := do
  let some fm ← r.manager.get
    | throw (IO.userError
        "Compose: FocusRequester has no focus manager — create it with \
         rememberFocusRequester inside a window's composition")
  match ← fm.findRequester r.id with
  | some n =>
    unless (← n.data).modifier.focusEnabled do
      throw (IO.userError
        "Compose: FocusRequester's node is not focusable — add Modifier.focusable")
    fm.requestFocus (some n)
  | none =>
    throw (IO.userError
      "Compose: FocusRequester is not attached — add Modifier.focusRequester \
       to the target node")

namespace Modifier

/-- Attach `r` to this node so `FocusRequester.requestFocus` targets it; the
node still needs `Modifier.focusable` to accept focus. Mirrors
`Modifier.focusRequester(focusRequester)`. -/
def focusRequester (r : FocusRequester) (m : Modifier := {}) : Modifier :=
  m.append (.focus (.requester r.id))

end Modifier

end Compose

end
