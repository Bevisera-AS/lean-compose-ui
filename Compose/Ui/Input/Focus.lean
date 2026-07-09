import Compose.Ui.Input.HitTest

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
that node was focused before). -/
def popModalScope (fm : FocusManager) (id : Nat) : IO Unit := do
  let st ← fm.savedFocus.get
  let saved := (st.find? (·.1 == id)).bind (·.2)
  fm.savedFocus.set (st.filter (·.1 != id))
  if saved.isSome then fm.requestFocus saved

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

end FocusManager

end Compose
