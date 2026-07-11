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
  return { log := ← MutableState.create #[], accent := ← MutableState.create 0,
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
  runComposeTest (body r) (width := 640) (height := 480) do
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
  runComposeTest (body r) (width := 640) (height := 480) do
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
  runComposeTest (body r) (width := 640) (height := 480) do
    click (.tag "btn-new")
    checkEq "toolbar New Window logged" (← r.log.get) #["New window opened"]
    checkEq "toolbar New Window fired hook" (← r.newWin.get) 1
    click (.tag "btn-about")
    checkEq "toolbar About fired hook" (← r.about.get) 1

/-! ## A tooltip appears only after the hover delay (frozen clock) -/

private def tooltip : IO Unit := do
  let r ← rig
  runComposeTest (body r) (width := 640) (height := 480) do
    assertMissing (.text "Open another window")
    moveTo (.tag "btn-new")
    advanceTimeBy 300                               -- short of the 500 ms delay
    assertMissing (.text "Open another window")
    advanceTimeBy 400                               -- now past it
    assertExists (.text "Open another window")

/-! ## The right-click context menu mutates visible state -/

private def contextMenu : IO Unit := do
  let r ← rig
  runComposeTest (body r) (width := 640) (height := 480) do
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

/-! ## The real application shell (`desktopApp` end to end, headless) -/

/-- The registry entry whose window has the given title, if any. -/
private def entryTitled (app : ApplicationScope) (t : String) :
    IO (Option WindowEntry) := do
  for e in ← app.windows.get do
    if (← e.ctx.window.getTitle) == t then return some e
  return none

/-- `entryTitled`, throwing when absent (test plumbing). -/
private def entryTitled! (app : ApplicationScope) (t : String) : IO WindowEntry := do
  match ← entryTitled app t with
  | some e => return e
  | none => throw (IO.userError s!"no live window titled '{t}'")

/-- Bounds (render px) of the unique node matching `m` in `e`'s window. -/
private def boundsIn (e : WindowEntry) (m : Matcher) : IO Rect := do
  let forest ← semanticsForest e.ctx.root
  let hits := forest.foldl (fun acc r => acc ++ r.flatten.filter m.test) #[]
  if h : hits.size = 1 then
    return hits[0].bounds
  else
    throw (IO.userError s!"expected one node matching {m.description} in \
      '{← e.ctx.window.getTitle}', found {hits.size}\nsemantics tree:\n\
      {dumpForest forest}")

/-- Click (press + release) the center of the unique matching node in `e`'s
window, routed through the application dispatcher by window id — the
production multi-window input path. -/
private def clickIn (app : ApplicationScope) (e : WindowEntry) (m : Matcher) :
    IO Unit := do
  let c := (← boundsIn e m).center
  let (x, y) ← (← e.ctx.sdlRenderer).coordinatesToWindow c.x c.y
  dispatchApplicationEvent app (.mouseButtonDown ⟨0, e.id, ⟨0⟩, .left, true, 1, x, y⟩)
  dispatchApplicationEvent app (.mouseButtonUp ⟨0, e.id, ⟨0⟩, .left, false, 1, x, y⟩)

/-- Boot the *real* `desktopApp` through `bootstrapApplication` and drive it
with clicks: New Window grows the registry, About opens the dialog, and OK
dismisses it — the demo's plain-do-block shell must recompose on its own
(the regression that shipped: without the application root scope, these
actions visibly did nothing). -/
private def applicationShell : IO Unit := do
  let app ← bootstrapApplication desktopApp
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "desktopApp boots one main window" (← app.windows.get).size 1
  let main ← entryTitled! app "Desktop"
  -- Toolbar "New Window" (real click, registry-routed): a second window opens.
  clickIn app main (.tag "btn-new")
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "New Window opens a second window" (← app.windows.get).size 2
  check "the extra window carries its id title"
    (← entryTitled app "Window #0").isSome
  -- Toolbar "About": the modal dialog appears…
  clickIn app main (.tag "btn-about")
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "About opens the dialog window" (← app.windows.get).size 3
  let about ← entryTitled! app "About"
  -- …and its OK button dismisses it (state-driven close).
  clickIn app about (.text "OK")
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "OK dismisses the About dialog" (← app.windows.get).size 2
  check "main and extra windows survive the dismissal"
    ((← entryTitled app "Desktop").isSome && (← entryTitled app "Window #0").isSome)
  (← app.composition).dispose
  checkEq "disposing tears every window down" (← app.windows.get).size 0

/-- The Desktop group. -/
def run : IO Unit := do
  scenario "menuActions" menuActions
  scenario "disabledAndEdit" disabledAndEdit
  scenario "toolbar" toolbar
  scenario "tooltip" tooltip
  scenario "contextMenu" contextMenu
  scenario "applicationShell" applicationShell

end Tests.Desktop
