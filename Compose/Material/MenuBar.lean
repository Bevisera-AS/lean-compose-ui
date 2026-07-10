import Compose.Material.Menu
import Compose.Material.Divider

namespace Compose

/-!
# In-window menu bar (`Compose/Material/MenuBar.lean`)

A desktop-style **menu bar** rendered inside the window — the Compose-Desktop
`MenuBar` analog for a toolkit whose backend (SDL3) has no native menu API.
A horizontal strip of top-level labels sits at the top of the window; clicking
a label drops its menu below it.

Because this framework's overlay layer is hit-tested as a single topmost path
(`LayoutNode.hitTest`), a dropdown's full-window dismiss backdrop would hide
the bar underneath it from pointer motion — so MenuBar does **not** reuse
`DropdownMenu`'s popup. Instead it owns a stable two-layer overlay stack while
open: a full-window **backdrop** (lowest) that both closes on an outside click
*and* runs the bar's hover-to-switch / click-to-toggle logic (it is the topmost
layer over the bar strip, which the dropdown never covers), and a **dropdown**
layer (above it) that reuses `Menu.lean`'s surface visuals — `shapes.medium`
outlined `Surface` around a `Column` of real `DropdownMenuItem`s, wired to a
shared `MenuState` for keyboard navigation. This fixed compose order keeps the
z-order stable across menu switches (no re-registration), so item clicks always
land on items and bar clicks always land on the backdrop.

Behavior (desktop menu-bar conventions):
* Click a label opens its menu; clicking the open label closes it.
* While any menu is open, moving over a different top-level label switches the
  open menu to it (mousedown-then-browse).
* An item click runs its action and closes everything; disabled items are inert;
  separators render as dividers.
* Esc and an outside click close.
* Keyboard (menu open): Up/Down move the highlight, Enter activates, Left/Right
  switch to the adjacent top-level menu, Esc closes.

MenuBar assumes it is placed at the window's top-left (the conventional spot);
label hit rectangles are captured in root coordinates via
`Modifier.onGloballyPositioned`, which the full-window backdrop shares.

Nested submenus (`.submenu`) are intentionally out of scope for M15: flat menus
with separators cover the desktop menu-bar need, and side-opening nested popups
would need their own hover/keyboard/dismiss coordination. The data model can
grow a `.submenu` case later without breaking `.item`/`.separator` callers.
-/

/-- One entry of a menu. Mirrors the leaf/divider cases of Compose-Desktop's
`MenuScope` (submenus omitted for M15 — see the module docstring). -/
inductive MenuElement where
  /-- A clickable menu item: `label`, its `onClick` action, and whether it is
  enabled (disabled items render dimmed and never fire). -/
  | item (label : String) (onClick : IO Unit) (enabled : Bool := true)
  /-- A horizontal divider between groups of items. -/
  | separator
  deriving Inhabited

/-- One top-level menu of a `MenuBar`: a bar `label` and its `items`. Named to
avoid colliding with `DropdownMenu`; anonymous-constructor friendly at call
sites (`{ label := "File", items := #[…] }`). Mirrors a Compose-Desktop `Menu`. -/
structure MenuBarMenu where
  /-- The text shown on the bar. -/
  label : String
  /-- The menu's entries, top to bottom. -/
  items : Array MenuElement
  deriving Inhabited

/-- Height of the menu bar strip (dp). -/
private def menuBarHeight : Dp := 36

/-- The bar's key handling while a menu is open (registered as an overlay
*capture* handler, so it runs before focused-node routing): Up/Down move the
highlight, Enter activates it, Left/Right switch to the adjacent top-level menu
(wrapping), Esc closes. A no-op while every menu is closed. -/
private def menuBarKeyHandler (openIndex : MutableState (Option Nat))
    (menu : MenuState) (count : Nat) : KeyEvent → IO Bool := fun ke => do
  unless ke.down do return false
  let some cur ← openIndex.cell.get | return false
  match ke.key with
  | .down => menu.move 1; return true
  | .up => menu.move (-1); return true
  | .left =>
    if count > 0 then
      menu.highlighted.set none
      openIndex.set (some ((cur + count - 1) % count))
    return true
  | .right =>
    if count > 0 then
      menu.highlighted.set none
      openIndex.set (some ((cur + 1) % count))
    return true
  | .return | .kpEnter =>
    if ke.isRepeat then return true
    menu.activateHighlighted
    return true
  | .escape => openIndex.set none; return true
  | _ => return false

/-- The full-window backdrop coroutine (lowest overlay layer). Over the bar
strip it is the topmost layer, so it drives hover-to-switch (motion over a label
switches the open menu) and click-to-toggle (a press on the open label closes,
on another label switches); a press anywhere else closes (click-away). The
dropdown layer sits above it, so item clicks never reach here. -/
private partial def menuBarBackdrop (labelRects : Array (MutableState Rect))
    (openIndex : MutableState (Option Nat)) (scope : PointerInputScope) :
    UiTask Unit := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .move =>
    if let some i ← hitLabel ev.position then
      unless (← openIndex.cell.get) == some i do openIndex.set (some i)
  | .press =>
    ev.consume
    match ← hitLabel ev.position with
    | some i => openIndex.set (if (← openIndex.cell.get) == some i then none else some i)
    | none => openIndex.set none
  | .release => ev.consume
  | _ => pure ()
  menuBarBackdrop labelRects openIndex scope
where
  /-- The index of the label whose captured rect contains `p` (root coords). -/
  hitLabel (p : Offset) : IO (Option Nat) := do
    let mut i := 0
    for rect in labelRects do
      let r ← rect.cell.get
      if r != Rect.zero && r.contains p then return some i
      i := i + 1
    return none

/-- Render one menu element inside an open dropdown: an `item` becomes a
`DropdownMenuItem` whose action runs and then closes the whole bar (disabled
items get an inert action, so neither a click nor keyboard Enter fires them); a
`separator` becomes a padded `HorizontalDivider`. -/
private def menuBarElement (openIndex : MutableState (Option Nat)) :
    MenuElement → Composable Unit
  | .item label onClick enabled =>
    DropdownMenuItem label
      (onClick := if enabled then (do onClick; openIndex.set none) else pure ())
      (enabled := enabled)
  | .separator =>
    Box HorizontalDivider
      (modifier := Modifier.fillMaxWidth |>.padding (vertical := some 4))

/-- The dropdown surface for the open menu: `Menu.lean`'s outlined
`shapes.medium` `Surface` around a `Column` of items, providing the shared
`MenuState` for keyboard navigation (reused, not duplicated). -/
private def menuBarDropdown (menu : MenuState) (items : Array MenuElement)
    (openIndex : MutableState (Option Nat)) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shapes ← MaterialTheme.shapes
  Surface (modifier := Modifier.widthIntrinsicMax |>.sizeIn (minWidth := some 112))
      (shape := shapes.medium)
      (color := some colors.surface)
      (border := some { width := 1, color := colors.outline }) do
    CompositionLocalProvider LocalMenuState (some menu) <|
      Column (modifier := Modifier.padding (vertical := some 8)) do
        for h in [0:items.size] do
          keyed h (menuBarElement openIndex items[h]!)

/-- One top-level label on the bar: opens its menu on click (while a menu is
open the backdrop handles bar clicks instead), captures its bounds for the
backdrop's hit test, and shows a hover/open state layer. -/
composable def menuBarLabel (index : Nat) (label : String)
    (openIndex : MutableState (Option Nat)) (rectState : MutableState Rect) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let source ← rememberInteractionSource
  let hovered ← source.hovered.get
  let active := (← openIndex.get) == some index || hovered
  let m := Modifier.onGloballyPositioned rectState.set
    |>.fillMaxHeight
    |>.clickable (openIndex.set (some index)) (source := some source)
    |>.background (if active then colors.onSurface.withAlpha 0.08 else .transparent)
    |>.padding (horizontal := some 12)
  Box (modifier := m) (contentAlignment := .center) do
    Text label (color := some colors.onSurface)

/-- An in-window desktop menu bar: a themed top strip of `menus` whose labels
drop their items below on click, with hover-to-switch, keyboard navigation, and
Esc / click-away dismissal (see the module docstring). Place it at the top of
the window. Mirrors Compose-Desktop's window `MenuBar`. -/
composable def MenuBar (menus : Array MenuBarMenu) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let ctx? ← LocalWindowContext.current
  let openIndex ← remember (mutableStateOf (none : Option Nat))
  let menuState ← remember MenuState.create
  let labelRects ← remember (menus.mapM (fun _ => mutableStateOf Rect.zero))
  let handlerId ← remember freshId
  -- Keyboard: one capture handler for the bar's lifetime, active only while a
  -- menu is open (Left/Right/Up/Down/Enter/Esc — see `menuBarKeyHandler`).
  DisposableEffect handlerId do
    match ctx? with
    | some ctx =>
      ctx.registerKeyHandler
        { id := handlerId, capture := true
          handler := menuBarKeyHandler openIndex menuState menus.size }
      return ctx.unregisterKeyHandler handlerId
    | none => return pure ()
  -- The bar strip: labels + a bottom divider, on the theme surface.
  Column (modifier := Modifier.fillMaxWidth |>.background colors.surface) do
    Row (modifier := Modifier.fillMaxWidth |>.height menuBarHeight) do
      for i in [0:menus.size] do
        if let some rs := labelRects[i]? then
          keyed i (menuBarLabel i menus[i]!.label openIndex rs)
    HorizontalDivider
  -- While open: a full-window backdrop (lowest — hover/click logic + click-away)
  -- then the dropdown for the open menu (above it). Fixed compose order keeps
  -- the z-order stable across menu switches.
  if let some i ← openIndex.get then
    withGroup 0x6d626f do
      Popup (onDismissRequest := none) do
        Spacer (Modifier.fillMaxSize
          |>.pointerInput (stringKey "Compose.MenuBar.backdrop")
              (menuBarBackdrop labelRects openIndex))
      let anchor ← match labelRects[i]? with
        | some rs => rs.get
        | none => pure Rect.zero
      Popup (menuBarDropdown menuState menus[i]!.items openIndex)
        (anchor := if anchor == Rect.zero then none else some anchor)
  else
    withGroup 0x6d626e (pure ())

end Compose
