import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# ContextMenu test group (`test/ComposeTests/ContextMenu.lean`)

MT coverage of `ContextMenuArea`: a right-click opens the menu (reusing
`DropdownMenu`), choosing an entry runs its action and closes, disabled
entries never fire, and Esc / click-away dismiss.
-/

namespace Tests.ContextMenu
open Compose Compose.Test Tests.Harness

/-- Build the test tree: a right-clickable area over `picked`, with a disabled
"Paste" entry wired to `disabledFired` so a stray activation is observable. -/
private def tree (picked : MutableState String) (disabledFired : IO.Ref Bool) :
    Composable Unit :=
  Tests.restartable 1 do
    Column {} (content := do
      ContextMenuArea
        #[{ label := "Cut", onClick := picked.set "Cut" },
          { label := "Copy", onClick := picked.set "Copy" },
          { label := "Paste", enabled := false, onClick := disabledFired.set true }]
        (modifier := Modifier.testTag "area")
        (content := Box (Modifier.size 80 40))
      Text s!"picked: {← picked.get}")

/-! ## Right-click opens; choosing an entry runs it and closes -/

private def openSelectClose : IO Unit := do
  let picked ← mutableStateOf "-"
  let disabledFired ← IO.mkRef false
  runComposeTest (content := tree picked disabledFired) do
    assertMissing (.role .menuItem)
    rightClick (.tag "area")
    settle                                -- let the enter transition finish
    assertCountEquals (.role .menuItem) 3
    click ((Matcher.text "Copy").and (.role .menuItem))
    assertExists (.text "picked: Copy")
    -- The exit transition keeps it mounted a moment, then it unmounts.
    settle
    assertMissing (.role .menuItem)

/-! ## Disabled entries render dimmed and never fire; the menu stays open -/

private def disabledDoesNotFire : IO Unit := do
  let picked ← mutableStateOf "-"
  let disabledFired ← IO.mkRef false
  runComposeTest (content := tree picked disabledFired) do
    rightClick (.tag "area")
    settle
    assertDisabled ((Matcher.text "Paste").and (.role .menuItem))
    click ((Matcher.text "Paste").and (.role .menuItem))
    check "disabled entry did not fire" (!(← disabledFired.get))
    assertExists (.text "picked: -")      -- unchanged
    assertExists (.role .menuItem)        -- still open (click was swallowed)

/-! ## Esc dismisses -/

private def escDismiss : IO Unit := do
  let picked ← mutableStateOf "-"
  let disabledFired ← IO.mkRef false
  runComposeTest (content := tree picked disabledFired) do
    rightClick (.tag "area")
    settle
    assertExists (.role .menuItem)
    pressKey .escape
    settle
    assertMissing (.role .menuItem)

/-! ## A click outside dismisses -/

private def clickAwayDismiss : IO Unit := do
  let picked ← mutableStateOf "-"
  let disabledFired ← IO.mkRef false
  runComposeTest (content := tree picked disabledFired) do
    rightClick (.tag "area")
    settle
    assertExists (.role .menuItem)
    -- A press landing off the menu hits the outside-click layer.
    clickAt ⟨4, 4⟩
    settle
    assertMissing (.role .menuItem)

/-- The ContextMenu group. -/
def run : IO Unit := do
  scenario "openSelectClose" openSelectClose
  scenario "disabledDoesNotFire" disabledDoesNotFire
  scenario "escDismiss" escDismiss
  scenario "clickAwayDismiss" clickAwayDismiss

end Tests.ContextMenu
