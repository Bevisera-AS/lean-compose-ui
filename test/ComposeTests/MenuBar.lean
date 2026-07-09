import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# MenuBar test group (`test/ComposeTests/MenuBar.lean`)

MT scenarios for the in-window desktop menu bar (`Compose.MenuBar`): a click
opens the right menu; hovering a different top-level label switches the open
menu (mousedown-then-browse); an item activates its action and closes; a
disabled item is inert; Esc and an outside click close; and keyboard navigation
(Down highlights, Enter activates the first item, Right switches to the next
menu, wrapping). Every scenario drives real SDL events through the production
input pipeline via the MT verbs.
-/

namespace Tests.MenuBar
open Compose Compose.Test Tests.Harness

/-- A two-menu bar (File: New / — / Quit, Edit: Copy / Paste[disabled]) whose
item actions bump counters, so scenarios can assert exactly what fired. -/
private structure Fixture where
  newRef : IO.Ref Nat
  quitRef : IO.Ref Nat
  copyRef : IO.Ref Nat
  pasteRef : IO.Ref Nat
  menus : Array MenuBarMenu

private def fixture : IO Fixture := do
  let newRef ← IO.mkRef 0
  let quitRef ← IO.mkRef 0
  let copyRef ← IO.mkRef 0
  let pasteRef ← IO.mkRef 0
  return {
    newRef, quitRef, copyRef, pasteRef
    menus := #[
      { label := "File", items := #[
          .item "New" (newRef.modify (· + 1)),
          .separator,
          .item "Quit" (quitRef.modify (· + 1)) ] },
      { label := "Edit", items := #[
          .item "Copy" (copyRef.modify (· + 1)),
          .item "Paste" (pasteRef.modify (· + 1)) (enabled := false) ] } ] }

/-- Click opens the clicked menu; hovering the other top-level label switches
to it while open; clicking the open label closes it. -/
private def openHoverSwitch : IO Unit := do
  let f ← fixture
  runComposeTest (content := MenuBar f.menus) do
    assertMissing (.role .menuItem)
    click (.text "File")
    settle
    assertExists (.text "New")
    assertExists (.text "Quit")
    assertMissing (.text "Copy")
    -- Separator is a divider, not a menu item: File contributes exactly two.
    assertCountEquals (.role .menuItem) 2
    -- Hover the other label while open → the menu switches to Edit.
    moveTo (.text "Edit")
    settle
    assertExists (.text "Copy")
    assertExists (.text "Paste")
    assertMissing (.text "New")
    -- Clicking the open label closes it.
    click (.text "Edit")
    settle
    assertMissing (.role .menuItem)

/-- An item click runs its action and closes everything; a disabled item is
inert and leaves the menu open. -/
private def activateAndDisabled : IO Unit := do
  let f ← fixture
  runComposeTest (content := MenuBar f.menus) do
    click (.text "File")
    settle
    click (.text "New")
    settle
    checkEq "item click fired its action" (← f.newRef.get) 1
    assertMissing (.role .menuItem)
    -- Disabled item: click does nothing and the menu stays open.
    click (.text "Edit")
    settle
    click (.text "Paste")
    settle
    checkEq "disabled item did not fire" (← f.pasteRef.get) 0
    assertExists (.text "Copy")
    -- An enabled sibling still works.
    click (.text "Copy")
    settle
    checkEq "enabled sibling fired" (← f.copyRef.get) 1
    assertMissing (.role .menuItem)

/-- Esc closes; an outside (empty-space) click closes. -/
private def dismiss : IO Unit := do
  let f ← fixture
  runComposeTest (content := MenuBar f.menus) do
    click (.text "File")
    settle
    pressKey .escape
    settle
    assertMissing (.role .menuItem)
    checkEq "Esc selected nothing" (← f.newRef.get) 0
    -- Reopen, then click far below the menu: click-away closes.
    click (.text "File")
    settle
    clickAt ⟨240, 300⟩
    settle
    assertMissing (.role .menuItem)

/-- Keyboard: Down highlights the first item, Enter activates it and closes;
Right switches to the next top-level menu (wrapping). -/
private def keyboardNav : IO Unit := do
  let f ← fixture
  runComposeTest (content := MenuBar f.menus) do
    click (.text "File")
    settle
    pressKey .down            -- highlight "New" (first item; separator skipped)
    pressKey .return          -- activate it
    settle
    checkEq "Down then Enter activated the first item" (← f.newRef.get) 1
    assertMissing (.role .menuItem)
    -- Right moves to the adjacent menu.
    click (.text "File")
    settle
    pressKey .right
    settle
    assertExists (.text "Copy")
    assertMissing (.text "New")
    -- Right wraps back around to the first menu.
    pressKey .right
    settle
    assertExists (.text "New")
    assertMissing (.text "Copy")

/-- The MenuBar group. -/
def run : IO Unit := do
  scenario "openHoverSwitch" openHoverSwitch
  scenario "activateAndDisabled" activateAndDisabled
  scenario "dismiss" dismiss
  scenario "keyboardNav" keyboardNav

end Tests.MenuBar
