import Compose.Material.Surface
import Compose.Material.Text
import Compose.Material.StateLayer
import Compose.Ui.Overlay
import Compose.Animation.Visibility

namespace Compose

open Draw

/-!
# Dropdown menus (`Compose/Material/Menu.lean`)

`DropdownMenu` + `DropdownMenuItem` + `ExposedDropdownMenuBox`, mirroring
their `androidx.compose.material3` namesakes on the M10 diet:

* The menu is a **focusable `Popup`** (outside-click + Esc dismissal via
  `onDismissRequest`; grabs key routing while open) holding an
  `AnimatedVisibility` (fade + expand vertically) around a bordered `Surface`
  (`shapes.medium`, `outline` border — no shadows in this renderer). The
  surface wraps its **widest item** (`Modifier.widthIntrinsicMax`, 112dp
  floor) — or the anchor's width with `matchAnchorWidth` — and the
  `fillMaxWidth` items stretch to exactly it. The
  enter transition plays because visibility flips one frame after the popup
  registers. On close the popup **stays mounted while the mirror-image exit
  transition (fade + shrink vertically) plays**, then unregisters — a short
  `UiTask.delay` past the animation keeps the overlay alive until it finishes;
  re-opening mid-exit cancels the unmount and animates back in.
* Keyboard: Down/Up move a highlighted item (wrapping), Enter activates it —
  intercepted before the focused anchor's own key handling. Hovering an item
  highlights it too.
* `ExposedDropdownMenuBox` captures its anchor rect via
  `Modifier.onGloballyPositioned` and hands content a scope with the anchor
  and an expansion toggle; `ExposedDropdownMenuField` is the read-only
  field-look anchor (Surface + value text + a drawn ▾ glyph) that toggles on
  click — enough for Flight Booker's combobox.
-/

/-- Shared state of one open menu: the registered items (in registration
order) and the keyboard/hover-highlighted item id. -/
structure MenuState where
  /-- `(item id, current onClick)` per composed item. -/
  items : IO.Ref (Array (Nat × IO.Ref (IO Unit)))
  /-- The highlighted item's id (observable — items recompose on change). -/
  highlighted : MutableState (Option Nat)

instance : Nonempty MenuState :=
  ⟨{ items := Classical.choice inferInstance
     highlighted := Classical.choice inferInstance }⟩

namespace MenuState

/-- Fresh, empty menu state. -/
def create : IO MenuState :=
  return { items := ← IO.mkRef #[], highlighted := ← MutableState.create none }

/-- Move the highlight by `delta` items (wrapping); from nothing, Down lands
on the first item and Up on the last. -/
def move (m : MenuState) (delta : Int) : IO Unit := do
  let items ← m.items.get
  if items.isEmpty then return
  let n := items.size
  let cur ← m.highlighted.cell.get
  let idx ← match cur with
    | some id =>
      match items.findIdx? (·.1 == id) with
      | some i => pure (((((i : Int) + delta) % (n : Int) + (n : Int)) % (n : Int)).toNat)
      | none => pure (if delta ≥ 0 then 0 else n - 1)
    | none => pure (if delta ≥ 0 then 0 else n - 1)
  if h : idx < items.size then
    m.highlighted.set (some items[idx].1)

/-- Run the highlighted item's current action, if any. -/
def activateHighlighted (m : MenuState) : IO Unit := do
  let some id ← m.highlighted.cell.get | return
  let items ← m.items.get
  if let some (_, action) := items.find? (·.1 == id) then
    (← action.get)

end MenuState

/-- Duration (ms) of the dropdown's enter/exit transitions; the overlay is
kept mounted a little past this while the exit plays. -/
private def dropdownAnimMs : Nat := 120

/-- Suspend on the frame clock until `durNs` has elapsed. Unlike
`UiTask.delay` this stays a frame-clock subscriber, so it drives the exit
window and headless `settle` advances through it. -/
private partial def awaitFramesFor (durNs : UInt64) : UiTask Unit := do
  let t0 ← UiTask.awaitFrame
  go t0
where
  go (t0 : UInt64) : UiTask Unit := do
    let ns ← UiTask.awaitFrame
    if ns < t0 + durNs then go t0

/-- The ambient state of the enclosing open `DropdownMenu` (`none` outside
one); `DropdownMenuItem` registers itself here. Internal plumbing analog of
material3's menu position/state internals. -/
initialize LocalMenuState : CompositionLocal (Option MenuState) ←
  return { id := ← freshId, defaultValue := none, isStatic := true,
           eq := fun _ _ => true }

/-- The menu's key handling while open (runs before focused-node routing):
Down/Up move the highlight, Enter activates it. -/
private def menuKeyHandler (menu : MenuState) : KeyEvent → IO Bool := fun ke => do
  unless ke.down do return false
  match ke.key with
  | .down => menu.move 1; return true
  | .up => menu.move (-1); return true
  | .return | .kpEnter =>
    if ke.isRepeat then return true
    menu.activateHighlighted
    return true
  | _ => return false

/-- A dropdown menu anchored below `anchor` (flipping above when out of
room): a focusable popup that dismisses on outside click / Esc and routes
Down/Up/Enter to its items while open. `expanded` drives it; closing is the
caller's job via `onDismissRequest` (and item `onClick`s). The menu is as
wide as its widest item (`Modifier.widthIntrinsicMax`, 112dp floor, at most
the window) with items stretching to exactly that width; `matchAnchorWidth`
instead fixes the width to the anchor's — the exposed-dropdown convention
(Material's `exposedDropdownSize`). Mirrors
`androidx.compose.material3.DropdownMenu`. -/
composable def DropdownMenu (expanded : Bool) (onDismissRequest : IO Unit)
    (content : Composable Unit := pure ())
    (anchor : Option Rect := none) (offset : IntOffset := ⟨0, 2⟩)
    (matchAnchorWidth : Bool := false) (modifier : Modifier := {}) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shapes ← MaterialTheme.shapes
  let density ← LocalDensity.current
  -- Width: the anchor's (exposed dropdown) or the widest item's — never the
  -- window's (the overlay measures popup content with window-sized max
  -- constraints, which `fillMaxWidth` items would otherwise stretch to).
  let widthMod :=
    match anchor with
    | some a =>
      if matchAnchorWidth && a.width > 0 then Modifier.width (density.pxToDp a.width)
      else Modifier.widthIntrinsicMax
    | none => Modifier.widthIntrinsicMax
  let menu ← remember MenuState.create
  -- Enter: the popup composes hidden, then the effect flips visibility on the
  -- next drain so AnimatedVisibility animates in. Exit: the popup stays
  -- mounted (`mounted`) while the exit plays, then a `UiTask.delay` past the
  -- animation unmounts it — re-opening mid-exit relaunches this effect,
  -- cancelling the unmount.
  let animSpec : AnimationSpec Float32 := .tween dropdownAnimMs 0 .fastOutSlowIn
  let vis ← remember (mutableStateOf false)
  let mounted ← remember (mutableStateOf expanded)
  liftM (m := IO) do if expanded then mounted.set true
  LaunchedEffect expanded do
    vis.set expanded
    unless expanded do
      menu.highlighted.set none
      awaitFramesFor ((dropdownAnimMs + 40) * 1_000_000).toUInt64
      mounted.set false
  if ← mounted.get then
    -- While exiting (mounted but no longer `expanded`) the popup is inert: it
    -- is visually fading but must not dismiss-catch clicks or grab keys, so a
    -- click/key aimed elsewhere is not swallowed by the dying menu. Re-opening
    -- flips `expanded` back true, restoring interactivity.
    Popup (anchor := anchor) (offset := offset)
      (onDismissRequest := some onDismissRequest) (focusable := true)
      (interactive := expanded)
      (onKeyEvent := menuKeyHandler menu) do
      let v ← vis.get
      AnimatedVisibility v
          (enter := fadeIn (spec := some animSpec) ++ expandVertically (spec := some animSpec))
          (exit := fadeOut (spec := some animSpec) ++ shrinkVertically (spec := some animSpec)) do
        Surface (modifier := modifier.then widthMod |>.sizeIn (minWidth := some 112))
            (shape := shapes.medium) (color := some colors.surface)
            (border := some { width := 1, color := colors.outline })
            (elevation := 3) do
          CompositionLocalProvider LocalMenuState (some menu) <|
            Column content (modifier := Modifier.padding (vertical := some 8))

/-- One menu entry: `text` + `onClick` (the caller closes the menu in
`onClick`/`onDismissRequest`). Hover or Down/Up highlight it (onSurface 8 %
layer); Enter activates the highlighted item. Mirrors
`androidx.compose.material3.DropdownMenuItem` (text-only M10 shape). -/
composable def DropdownMenuItem (text : String) (onClick : IO Unit)
    (enabled : Bool := true) (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let menu? ← LocalMenuState.current
  let id ← remember freshId
  let actionRef ← rememberUpdatedRef onClick
  -- Register with the enclosing menu (composition order) for keyboard nav.
  DisposableEffect id do
    if let some menu := menu? then
      menu.items.modify (·.push (id, actionRef))
    return do
      if let some menu := menu? then
        menu.items.modify (·.filter (·.1 != id))
        menu.highlighted.modify fun h => if h == some id then none else h
  let source ← rememberInteractionSource
  let hovered ← source.hovered.get
  LaunchedEffect (hovered && enabled) do
    if hovered && enabled then
      if let some menu := menu? then menu.highlighted.set (some id)
  let highlighted ← match menu? with
    | some menu => do pure ((← menu.highlighted.get) == some id)
    | none => pure false
  let m := modifier
    |>.fillMaxWidth
    |>.sizeIn (minWidth := some 112) (minHeight := some 36)
    |>.semantics (role := some .menuItem)
    |>.clickable (do (← actionRef.get)) enabled (source := some source)
    |>.background (if highlighted && enabled then colors.onSurface.withAlpha 0.08
                   else .transparent)
    |>.padding (horizontal := some 12) (vertical := some 8)
  Box (modifier := m) (contentAlignment := .centerStart) do
    Text text (color := some (if enabled then colors.onSurface
                              else colors.onSurface.withAlpha disabledContentAlpha))

/-- Receiver scope of `ExposedDropdownMenuBox` content: the captured anchor
rect (window coordinates) and the expansion toggle. Mirrors
`ExposedDropdownMenuBoxScope`. -/
structure ExposedDropdownMenuBoxScope where
  /-- The box's window-coordinate bounds (zero before the first frame). -/
  anchorRect : MutableState Rect
  /-- Latest `expanded` (for `toggle`). -/
  expandedRef : IO.Ref Bool
  /-- Latest `onExpandedChange`. -/
  onExpandedChangeRef : IO.Ref (Bool → IO Unit)

instance : Nonempty ExposedDropdownMenuBoxScope :=
  ⟨{ anchorRect := Classical.choice inferInstance
     expandedRef := Classical.choice inferInstance
     onExpandedChangeRef := Classical.choice inferInstance }⟩

namespace ExposedDropdownMenuBoxScope

/-- The anchor rect for the enclosed `DropdownMenu` (`none` before the box
was first positioned). Observed read — repositioning recomposes. -/
def anchor (s : ExposedDropdownMenuBoxScope) : Composable (Option Rect) := do
  let r ← s.anchorRect.get
  return if r == Rect.zero then none else some r

/-- Flip the expansion through the latest `onExpandedChange`. -/
def toggle (s : ExposedDropdownMenuBoxScope) : IO Unit := do
  (← s.onExpandedChangeRef.get) !(← s.expandedRef.get)

end ExposedDropdownMenuBoxScope

/-- Pairs an anchor (compose it in `content`, e.g.
`ExposedDropdownMenuField`) with its `DropdownMenu`: captures the anchor
rect via `Modifier.onGloballyPositioned` and provides it (plus an expansion
toggle) through the scope. Pass the enclosed `DropdownMenu`
`matchAnchorWidth := true` so the menu matches the field's width (Material's
exposed-dropdown convention). Mirrors
`androidx.compose.material3.ExposedDropdownMenuBox`. -/
composable def ExposedDropdownMenuBox (expanded : Bool)
    (onExpandedChange : Bool → IO Unit)
    (content : ExposedDropdownMenuBoxScope → Composable Unit := fun _ => pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  let scope : ExposedDropdownMenuBoxScope ← remember do
    pure { anchorRect := ← MutableState.create Rect.zero
           expandedRef := ← IO.mkRef expanded
           onExpandedChangeRef := ← IO.mkRef onExpandedChange }
  scope.expandedRef.set expanded
  scope.onExpandedChangeRef.set onExpandedChange
  Box (content scope)
    (modifier := modifier.onGloballyPositioned scope.anchorRect.set)

/-- The ▾ trailing glyph of `ExposedDropdownMenuField`, drawn with two lines
(no icon font). Flips ▴ while expanded. -/
private def trailingTriangle (color : Color) (expanded : Bool) : Composable Unit :=
  Spacer (Modifier.size 12 12 |>.drawBehind do
    let (yTop, yBot) : Float32 × Float32 := if expanded then (8, 4) else (4, 8)
    DrawScope.drawLine (.solid color) ⟨2, yTop⟩ ⟨6, yBot⟩ 1.5
    DrawScope.drawLine (.solid color) ⟨6, yBot⟩ ⟨10, yTop⟩ 1.5)

/-- The read-only, field-look anchor for `ExposedDropdownMenuBox`: an
outlined Surface showing the selected `value` with a trailing ▾ glyph;
clicking (or Enter/Space when focused) toggles the menu. Mirrors the
`menuAnchor`+read-only-`TextField` idiom of material3's exposed dropdown
(Flight Booker's combobox). -/
composable def ExposedDropdownMenuField (scope : ExposedDropdownMenuBoxScope)
    (value : String) (expanded : Bool := false) (modifier : Modifier := {}) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shapes ← MaterialTheme.shapes
  let source ← rememberInteractionSource
  let focused ← source.focused.get
  let m := modifier
    |>.sizeIn (minWidth := some 160) (minHeight := some 40)
    |>.clickable scope.toggle (source := some source)
    |>.background colors.surface shapes.extraSmall
    |>.border (if focused then 2 else 1)
        (if focused then colors.primary else colors.outline) shapes.extraSmall
    |>.padding (horizontal := some 12) (vertical := some 8)
  Row (modifier := m) (verticalAlignment := .centerVertically) do
    Text value (color := some colors.onSurface)
    Spacer (Modifier.weight 1 |>.height 1)
    trailingTriangle colors.onSurfaceVariant expanded

end Compose
