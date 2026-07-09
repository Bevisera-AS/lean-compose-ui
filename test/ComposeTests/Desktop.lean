import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier
import Demos.Desktop

/-!
# Desktop demo behavior tests (`test/ComposeTests/Desktop.lean`)

MT coverage of the desktop-components demo's *wiring* (`Demos/Desktop.lean`).
The main window's content — `desktopBody` — is mounted with **recording hooks**
(the window/dialog/quit side effects) and injected shared state, so we assert
the demo's own logic without opening OS windows (multi-window behavior itself is
covered by the `MultiWindow` group). We drive real SDL events through the
production input pipeline via the MT verbs, and read the shared state back.

Menu labels ("New Window", "About") are duplicated by toolbar buttons, so menu
clicks match on `.role .menuItem` to stay unambiguous.
-/

namespace Tests.Desktop
open Compose Compose.Test Tests.Harness Demos.Desktop

/-- Injected shared state + recording hooks for one scenario. -/
private structure Rig where
  log : MutableState (Array String)
  accent : MutableState Nat
  newWin : IO.Ref Nat
  about : IO.Ref Nat
  quit : IO.Ref Nat

private def rig : IO Rig := do
  return { log := ← mutableStateOf #[], accent := ← mutableStateOf 0,
           newWin := ← IO.mkRef 0, about := ← IO.mkRef 0, quit := ← IO.mkRef 0 }

/-- Mount `desktopBody` on a rig's state, its hooks counting invocations. -/
private def body (r : Rig) : Composable Unit :=
  desktopBody r.log r.accent
    (onNewWindow := r.newWin.modify (· + 1))
    (onAbout := r.about.modify (· + 1))
    (onQuit := r.quit.modify (· + 1))

/-- A menu item (disambiguated from same-labeled toolbar buttons). -/
private def item (label : String) : Matcher := (Matcher.text label).and (.role .menuItem)

/-! ## Menu actions mutate visible state and fire the right hook -/

private def menuActions : IO Unit := do
  let r ← rig
  runComposeTest (content := body r) (width := 640) (height := 480) do
    assertMissing (.role .menuItem)
    -- File ▸ New Window: logs a line *and* fires the window hook.
    click (.text "File"); settle
    click (item "New Window"); settle
    checkEq "menu New Window logged" (← r.log.get) #["New window opened"]
    checkEq "menu New Window fired hook" (← r.newWin.get) 1
    assertMissing (.role .menuItem)                 -- item click closed the menu
    -- Help ▸ About: fires the about hook.
    click (.text "Help"); settle
    click (item "About"); settle
    checkEq "menu About fired hook" (← r.about.get) 1
    -- File ▸ Quit: fires the quit hook.
    click (.text "File"); settle
    click (item "Quit"); settle
    checkEq "menu Quit fired hook" (← r.quit.get) 1

/-! ## A disabled menu item is inert; enabled siblings work -/

private def disabledAndEdit : IO Unit := do
  let r ← rig
  runComposeTest (content := body r) (width := 640) (height := 480) do
    click (.text "Edit"); settle
    assertDisabled (item "Cut")
    click (item "Cut"); settle
    checkEq "disabled Cut did nothing" (← r.log.get) #[]
    assertExists (.role .menuItem)                  -- disabled click keeps it open
    click (item "Add Note"); settle
    checkEq "Add Note logged" (← r.log.get) #["Note added"]
    -- Clear Log empties the shared log.
    click (.text "Edit"); settle
    click (item "Clear Log"); settle
    checkEq "Clear Log emptied the log" (← r.log.get) #[]

/-! ## Toolbar buttons mirror the menu actions -/

private def toolbar : IO Unit := do
  let r ← rig
  runComposeTest (content := body r) (width := 640) (height := 480) do
    click (.tag "btn-new")
    checkEq "toolbar New Window logged" (← r.log.get) #["New window opened"]
    checkEq "toolbar New Window fired hook" (← r.newWin.get) 1
    click (.tag "btn-about")
    checkEq "toolbar About fired hook" (← r.about.get) 1

/-! ## A tooltip appears only after the hover delay (frozen clock) -/

private def tooltip : IO Unit := do
  let r ← rig
  runComposeTest (content := body r) (width := 640) (height := 480) do
    assertMissing (.text "Open another window")
    moveTo (.tag "btn-new")
    advanceTimeBy 300                               -- short of the 500 ms delay
    assertMissing (.text "Open another window")
    advanceTimeBy 400                               -- now past it
    assertExists (.text "Open another window")

/-! ## The right-click context menu mutates visible state -/

private def contextMenu : IO Unit := do
  let r ← rig
  runComposeTest (content := body r) (width := 640) (height := 480) do
    assertExists (.text "Right-click me — accent: Blue")
    rightClick (.tag "canvas"); settle
    assertExists (.role .menuItem)
    click (item "Green accent"); settle
    checkEq "context menu set the accent" (← r.accent.get) 1
    assertExists (.text "Right-click me — accent: Green")
    assertMissing (.role .menuItem)                 -- choosing closed it
    -- The "Add log entry" entry appends to the shared log.
    rightClick (.tag "canvas"); settle
    click (item "Add log entry"); settle
    checkEq "context menu logged" (← r.log.get) #["Context action"]

/-- The Desktop group. -/
def run : IO Unit := do
  scenario "menuActions" menuActions
  scenario "disabledAndEdit" disabledAndEdit
  scenario "toolbar" toolbar
  scenario "tooltip" tooltip
  scenario "contextMenu" contextMenu

end Tests.Desktop
