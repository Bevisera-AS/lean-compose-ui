module

public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Ui.App
public meta import Compose.Ui.App

public section

namespace Compose

/-!
# App-level theming (`Compose/Material/App.lean`)

The seam between the Material theme and the app shell: `AppTheme` selects a
theme (fixed, or following the OS light/dark setting), `MaterialApp` installs
it at the root of a composition, `syncWindowClearColor` points a window's
clear color at the ambient scheme, and `runMaterialApp` is the single-window
`runApp` with both wired up.

`AppTheme.system` reads `isSystemInDarkTheme`, which is *live*: an OS theme
flip while the app runs recomposes the theme provider and every reader with
it. First frames are correct too — `bootstrapWindow` seeds the dark-mode
state before creating the composition, and composition precedes the first
render, so no light-themed frame can flash on a dark desktop.

Multi-window apps compose `MaterialApp` once around the app-level content
(`Compose.application`): each `Window` captures the CompositionLocals at its
call site, so every window's subtree inherits the app theme. Windows that
also want a theme-matched clear color compose `syncWindowClearColor` at the
top of their content — `runMaterialApp` does it for its one window.
-/

/-- Which theme an app runs. `.system` follows the OS light/dark setting and
tracks it live. Mirrors the `isSystemInDarkTheme()`-switching root of a
Compose app, as data. -/
inductive AppTheme where
  /-- Always this theme, whatever the OS says. -/
  | fixed (theme : Theme)
  /-- Follow the OS light/dark setting, live. -/
  | system (light : Theme := .light) (dark : Theme := .dark)
  deriving Repr, BEq, Inhabited

/-- The theme this selection resolves to right now. `.system` reads
`isSystemInDarkTheme`, so readers recompose when the OS theme flips. -/
def AppTheme.resolve : AppTheme → Composable Theme
  | .fixed theme => pure theme
  | .system light dark => return if ← isSystemInDarkTheme then dark else light

/-- Point the ambient window's clear color at the ambient scheme's `surface`,
so the frame's background matches the theme; a no-op outside a window (the
app-level composition of `Compose.application` has no window of its own).
Compose it *inside* the theme provider, at the top of a `Window`'s content.
Re-runs every composition and writes a plain `IO.Ref`, so it is idempotent. -/
def syncWindowClearColor : Composable Unit := do
  if let some ctx ← LocalWindowContext.current then
    ctx.clearColor.set (← MaterialTheme.colorScheme).surface

/-- App-level themed root: resolve `theme` and install it, so every `Window`
composed inside inherits it through the call-site CompositionLocal capture.
Use it once around a `Compose.application` composition; the single-window
`runMaterialApp` wraps its content in one for you.

Windows wanting a theme-matched clear color compose `syncWindowClearColor` in
their own content — `MaterialApp` itself emits nothing, which is what lets it
sit in the app-level composition (where widgets are illegal). -/
composable def MaterialApp (content : Composable Unit) (theme : AppTheme := .system) :
    Composable Unit := do
  MaterialTheme content (theme := some (← theme.resolve))

/-- `runApp` with the theme installed and the window's clear color kept in
sync with the scheme's `surface`. The default `.system` theme follows the OS
light/dark setting, live and correct from the first frame. Mirrors
`singleWindowApplication { MaterialTheme { … } }`. -/
def runMaterialApp (title : String) (width height : Dp) (content : Composable Unit)
    (theme : AppTheme := .system) (config : AppConfig := {}) : IO UInt32 :=
  runApp title width height
    (MaterialApp (theme := theme) do syncWindowClearColor; content) config

end Compose

end
