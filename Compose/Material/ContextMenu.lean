import Compose.Material.Menu

namespace Compose

/-!
# Context menu (`Compose/Material/ContextMenu.lean`)

`ContextMenuArea`, mirroring Compose Desktop's
`androidx.compose.foundation.ContextMenuArea` — a secondary (right) click
inside `content` opens a menu at the click point:

* The gesture is a dedicated secondary-tap detector (the `onSecondaryTap`
  branch of `detectTapGestures`, extracted so it claims **only** right-button
  presses — primary clicks pass through unconsumed and keep working on
  ancestor clickables). The click position (content-local) is lifted to
  window coordinates via the captured content rect and used as the menu
  anchor.
* The menu itself **is** a `DropdownMenu`, so it inherits Menu.lean wholesale:
  the elevated bordered `Surface`, the enter/exit transitions, click-away and
  Esc dismissal, and Down/Up/Enter keyboard nav. Items come from a plain data
  DSL (`ContextMenuItem`) rather than Compose Desktop's `() -> List<…>` lambda
  — recomposition freshness is fine here because the menu closes on every item
  activation, so a stale action array cannot outlive an open menu.
-/

/-- One context-menu entry: its `label`, whether it is `enabled`, and the
`onClick` action run on selection. The Lean-idiomatic data form of Compose
Desktop's `ContextMenuItem(label) { onClick }`. -/
structure ContextMenuItem where
  /-- The entry's text. -/
  label : String
  /-- Whether the entry is selectable (disabled entries render dimmed and
  never fire). -/
  enabled : Bool := true
  /-- Action run when the entry is chosen (the menu closes afterwards). -/
  onClick : IO Unit
  deriving Inhabited

/-- Await events until the pressed button ends: a `release` (consumed) or an
`exit` (`none`). The private helper of `detectTapGestures`, restated for the
right-button-only detector below. -/
private partial def awaitRelease (scope : PointerInputScope) :
    UiTask (Option PointerEvent) := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .release => ev.consume; return some ev
  | .exit => return none
  | _ => awaitRelease scope

/-- Detect completed right-button clicks *only*: a right press is consumed and
`onSecondaryTap` fires on its release inside the element; every other event —
crucially primary presses — passes through unconsumed, so ancestor clickables
behave as if the area weren't there. (`detectTapGestures` consumes every
press, which would swallow left clicks meant for ancestors.) -/
private partial def detectSecondaryTap (onSecondaryTap : Offset → IO Unit)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press && ev.button == some .right then
    ev.consume
    if let some rel ← awaitRelease scope then
      if ← scope.containsLocal rel.position then
        onSecondaryTap rel.position
  detectSecondaryTap onSecondaryTap scope

/-- Wrap `content` so a right-click inside it opens `items` in a `DropdownMenu`
anchored at the click point: click-away or Esc dismisses, choosing an entry
runs its `onClick` then closes, and disabled entries never fire. Mirrors
`androidx.compose.foundation.ContextMenuArea`. -/
composable def ContextMenuArea (items : Array ContextMenuItem)
    (content : Composable Unit) (modifier : Modifier := {}) : Composable Unit := do
  let expanded ← remember (mutableStateOf false)
  let anchor ← remember (mutableStateOf Offset.zero)
  let rectRef ← remember (IO.mkRef Rect.zero)
  let id ← remember freshId
  let onSecondary : Offset → IO Unit := fun loc => do
    let r ← rectRef.get
    anchor.set ⟨r.left + loc.x, r.top + loc.y⟩
    expanded.set true
  let m := modifier.onGloballyPositioned rectRef.set
    |>.pointerInput (mixKeys (stringKey "Compose.ContextMenuArea") id.toUInt64)
        (detectSecondaryTap onSecondary)
  Box content (modifier := m)
  let a ← anchor.get
  DropdownMenu (← expanded.get) (onDismissRequest := expanded.set false)
      (anchor := some ⟨a.x, a.y, a.x, a.y⟩) (offset := ⟨0, 0⟩) do
    for i in [0:items.size] do
      let it : ContextMenuItem := items[i]!
      keyed i <|
        DropdownMenuItem it.label (enabled := it.enabled)
          (onClick := if it.enabled then do it.onClick; expanded.set false
                      else pure ())

end Compose
