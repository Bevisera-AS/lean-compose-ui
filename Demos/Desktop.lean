import Compose

/-!
# Desktop components demo (`lake exe demo-desktop`)

A showcase of the M15 desktop widgets driven by `Compose.application`:

* a declarative main **`Window`** whose **`MenuBar`** (File / Edit / Help) opens
  extra windows, toggles state, and pops an **About `DialogWindow`**;
* **`Tooltip`s** on the toolbar buttons;
* a **`ContextMenuArea`** canvas whose right-click menu recolors the accent /
  appends to the activity log;
* a **`Tray`** icon whose menu mirrors a couple of actions and a checkbox — its
  creation is best-effort, so a headless driver simply gets no icon;
* a shared **activity log** so menu, toolbar, tray, and window actions all leave
  a visible trace.

The design mirrors `Demos/Gallery.lean`: the main window's *content* is the
main-free `desktopBody` composable, parameterized by the shared visible state
and by the window/dialog/quit **hooks** (which would open OS windows). The MT
suite (`test/ComposeTests/Desktop.lean`) mounts `desktopBody` with recording
hooks to assert the demo's wiring without forking windows; `desktopApp` supplies
the real hooks and the multi-window plumbing. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-desktop`.
-/

namespace Demos.Desktop
open Compose

/-- The selectable accent swatches: a display name and its fill color. The
context menu sets the active index. -/
def accents : Array (String × Color) :=
  #[("Blue",  .rgb8 0x42 0x85 0xf4),
    ("Green", .rgb8 0x34 0xa8 0x53),
    ("Amber", .rgb8 0xf9 0xab 0x00),
    ("Red",   .rgb8 0xea 0x43 0x35)]

/-- The active accent (name, color), clamped so an out-of-range index is safe. -/
def accentAt (i : Nat) : String × Color := accents[i]! -- callers keep `i < accents.size`

/-! ## Main-window content (the tested composable) -/

/-- The main window's content: a `MenuBar`, a tooltip'd toolbar, a right-click
`ContextMenuArea` canvas, and the shared activity log. Visible state
(`log`/`accent`) is mutated here; the `on*` hooks perform the window/dialog/quit
side effects — injected so the MT suite can record them instead of opening OS
windows. Compose it under a theme (`desktopApp` installs one app-wide with
`MaterialApp`; `runComposeTest` provides its own). -/
composable def desktopBody
    (log : MutableState (Array String)) (accent : MutableState Nat)
    (onNewWindow : IO Unit) (onAbout : IO Unit) (onQuit : IO Unit) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let entries ← log.get
  let (accentName, accentColor) := accentAt (← accent.get)
  let newWindow : IO Unit := do log.modify (·.push "New window opened"); onNewWindow
  Column (modifier := Modifier.fillMaxSize) do
    MenuBar #[
      { label := "File", items := #[
          .item "New Window" newWindow,
          .separator,
          .item "Quit" onQuit ] },
      { label := "Edit", items := #[
          .item "Add Note" (log.modify (·.push "Note added")),
          .item "Cut" (pure ()) (enabled := false),   -- inert placeholder
          .separator,
          .item "Clear Log" (log.set #[]) ] },
      { label := "Help", items := #[
          .item "About" onAbout ] } ]
    Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12) do
      Text "Desktop components" (style := { fontSize := 20, weight := .bold })
      -- Tooltip'd toolbar buttons (duplicating two menu actions).
      Row (horizontalArrangement := .spacedBy 12) do
        Tooltip "Open another window" (modifier := Modifier.testTag "tt-new") do
          Button newWindow (Text "New Window") (modifier := Modifier.testTag "btn-new")
        Tooltip "Show the about dialog" (modifier := Modifier.testTag "tt-about") do
          Button onAbout (Text "About") (modifier := Modifier.testTag "btn-about")
      -- Right-click canvas: recolor the accent or append to the log.
      ContextMenuArea
        #[{ label := "Blue accent",  onClick := accent.set 0 },
          { label := "Green accent", onClick := accent.set 1 },
          { label := "Amber accent", onClick := accent.set 2 },
          { label := "Red accent",   onClick := accent.set 3 },
          { label := "Add log entry", onClick := log.modify (·.push "Context action") }]
        (modifier := Modifier.testTag "canvas") do
        Surface (modifier := Modifier.fillMaxWidth |>.height 84) (shape := .rounded 12)
            (color := some accentColor) do
          Box (modifier := Modifier.padding (all := 14)) do
            Text s!"Right-click me — accent: {accentName}"
              (color := some .white)
      -- Shared activity log.
      Text "Activity log" (style := { fontSize := 14, weight := .medium })
      Column (modifier := Modifier.testTag "log" |>.fillMaxWidth)
          (verticalArrangement := .spacedBy 2) do
        if entries.isEmpty then
          Text "(empty)" (color := some colors.onSurfaceVariant)
        else
          entries.forM (fun line => Text s!"• {line}")

/-! ## Extra windows + about dialog + the application shell -/

/-- A secondary `Window`'s content: it shares the app's activity log, so a
button here shows cross-window shared state. -/
composable def extraWindowBody (id : Nat) (log : MutableState (Array String)) :
    Composable Unit :=
  Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 10) do
    Text s!"Extra window #{id}" (style := { fontSize := 16, weight := .medium })
    Text "Closing me closes just this window."
    Button (log.modify (·.push s!"Note from window #{id}")) (Text "Log a note")

/-- The About dialog body: a line of text and an OK button that runs `onOk`
(which closes the dialog and logs the dismissal). -/
composable def aboutBody (onOk : IO Unit) : Composable Unit :=
  Column (modifier := Modifier.padding (all := 20)) (verticalArrangement := .spacedBy 16) do
    Text "compose-ui desktop demo" (style := { fontSize := 16, weight := .bold })
    Text "Multi-window, menu bar, context menu, tooltips, and a system tray."
    Row (modifier := Modifier.fillMaxWidth) (horizontalArrangement := .end) do
      Button onOk (Text "OK")

/-- The application shell: owns the shared state, declares the main `Window`,
the state-driven array of extra `Window`s, the About `DialogWindow`, and a
`Tray`. Run it via `Compose.application` (see `Demos/DesktopMain.lean`).

`MaterialApp` installs one theme app-wide — every `Window` inherits it through
its call-site locals capture — and each window's content opens with
`syncWindowClearColor` so its background follows the scheme. -/
def desktopApp : Composable Unit := MaterialApp do
  let log ← remember (mutableStateOf (#[] : Array String))
  let accent ← remember (mutableStateOf 0)
  let windows ← remember (mutableStateOf (#[] : Array Nat))  -- live extra-window ids
  let nextId ← remember (mutableStateOf 0)
  let aboutOpen ← remember (mutableStateOf false)
  let verbose ← remember (mutableStateOf false)
  let quit ← exitApplication
  let onNewWindow : IO Unit := do
    let id ← nextId.get
    nextId.set (id + 1)
    windows.modify (·.push id)
  let closeAbout : IO Unit := do
    aboutOpen.set false
    log.modify (·.push "About dismissed")
  -- Main window: closing it exits the whole application.
  Window "Desktop" 640 480 (onCloseRequest := do quit; pure true)
    (do syncWindowClearColor
        desktopBody log accent onNewWindow (aboutOpen.set true) quit)
  -- Extra windows, each independently closable.
  for id in ← windows.get do
    keyed id (Window s!"Window #{id}" 340 220
      (onCloseRequest := do windows.modify (·.filter (· != id)); pure true)
      (do syncWindowClearColor; extraWindowBody id log))
  -- About: a modal dialog of the main window.
  if ← aboutOpen.get then
    DialogWindow "About" 360 200 (onCloseRequest := do closeAbout; pure true)
      (do syncWindowClearColor; aboutBody closeAbout)
  -- System tray (best-effort; absent under headless drivers).
  Tray (tooltip := some "compose-ui desktop") (menu := #[
    .item "Add log entry" (log.modify (·.push "Tray action")),
    .item "Verbose" (verbose.modify not) (checked := some (← verbose.get)),
    .separator,
    .item "Quit" quit ])

end Demos.Desktop
