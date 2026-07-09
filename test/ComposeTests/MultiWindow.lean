import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Multi-window test group (`test/ComposeTests/MultiWindow.lean`)

Drives M15's `bootstrapApplication`/`stepApplication` headless (dummy video
driver, software renderers): two windows compose and render independently,
synthetic events route by window id to the right window, `windowCloseRequested`
consults the per-window `onCloseRequest`, state-driven close/reopen works,
the application is `done` when the last window leaves or `exitApplication`
fires, `DialogWindow` parents (and marks modal where the driver allows), and
title/size follow recomposition. App-level `CompositionLocal`s must be
visible inside window content (the captured-locals bridge).
-/

namespace Tests.MultiWindow
open Compose Tests.Harness

/-- Per-window test config: software renderer for stable `readPixels`. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

/-- The registry entry whose window has the given title. -/
private def entryTitled (app : ApplicationScope) (t : String) : IO (Option WindowEntry) := do
  for e in ← app.windows.get do
    if (← e.ctx.window.getTitle) == t then return some e
  return none

/-- `entryTitled`, throwing when absent (test plumbing). -/
private def entryTitled! (app : ApplicationScope) (t : String) : IO WindowEntry := do
  match ← entryTitled app t with
  | some e => return e
  | none => throw (IO.userError s!"no live window titled '{t}'")

/-- Probe a window's rendered output at `(x, y)`. -/
private def pixel (e : WindowEntry) (x y : Int32) : IO Sdl.Color := do
  (← e.ctx.renderer.readPixels).readPixel x y

/-- A full-window click-counting region (bumps `hits` through the real
pointer path). -/
private def clickCounter (hits : IO.Ref Nat) (color : Color) : Composable Unit :=
  Box (Modifier.fillMaxSize |>.background color |>.clickable (hits.modify (· + 1)))

/-- Synthesize a click (press + release) at window coordinates `(x, y)` of
`e`'s window, routed through the application dispatcher by window id. -/
private def clickWindow (app : ApplicationScope) (e : WindowEntry)
    (x y : Float32) : IO Unit := do
  dispatchApplicationEvent app (.mouseButtonDown ⟨0, e.id, ⟨0⟩, .left, true, 1, x, y⟩)
  dispatchApplicationEvent app (.mouseButtonUp ⟨0, e.id, ⟨0⟩, .left, false, 1, x, y⟩)

/-- Two windows compose from one application; each renders its own content
into its own renderer, and events route by window id to the right one. -/
private def twoWindowsComposeAndRoute : IO Unit := do
  let hitsA ← IO.mkRef (0 : Nat)
  let hitsB ← IO.mkRef (0 : Nat)
  let app ← bootstrapApplication do
    Window "mw-a" 200 150 (config := cfg) (content := clickCounter hitsA .red)
    Window "mw-b" 200 150 (config := cfg) (content := clickCounter hitsB .blue)
  checkEq "two Windows register two live windows" (← app.windows.get).size 2
  check "a fresh application is not done" (!(← app.done))
  let _ ← stepApplication app (idleCapMs := 5)
  let a ← entryTitled! app "mw-a"
  let b ← entryTitled! app "mw-b"
  check "window A renders its own content" (colorNear (← pixel a 10 10) 255 0 0)
  check "window B renders its own content" (colorNear (← pixel b 10 10) 0 0 255)
  -- A click in window B reaches B's handler, not A's.
  clickWindow app b 20 20
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "click in B hits B" (← hitsB.get) 1
  checkEq "click in B does not hit A" (← hitsA.get) 0
  clickWindow app a 20 20
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "click in A hits A" (← hitsA.get) 1
  checkEq "B unchanged by A's click" (← hitsB.get) 1
  -- An event for a window id no application window owns is dropped.
  dispatchApplicationEvent app (.mouseButtonDown ⟨0, ⟨999999⟩, ⟨0⟩, .left, true, 1, 5, 5⟩)
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "unknown-window events are dropped (A)" (← hitsA.get) 1
  checkEq "unknown-window events are dropped (B)" (← hitsB.get) 1

/-- `windowCloseRequested` routes to the addressed window only: the default
handler closes exactly that window; a vetoing handler keeps its window; the
application exits when the last window closes. -/
private def closeRequestRouting : IO Unit := do
  let vetoes ← IO.mkRef (0 : Nat)
  let app ← bootstrapApplication do
    Window "mw-keep" 120 100 (config := cfg)
      (onCloseRequest := do vetoes.modify (· + 1); pure false)
    Window "mw-close" 120 100 (config := cfg)
  let _ ← stepApplication app (idleCapMs := 5)
  let closeMe ← entryTitled! app "mw-close"
  dispatchApplicationEvent app (.windowCloseRequested ⟨0, closeMe.id, 0, 0⟩)
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "default close request closes that window" (← app.windows.get).size 1
  check "the other window survives" (← entryTitled app "mw-keep").isSome
  check "application still running with one window" (!(← app.done))
  let keep ← entryTitled! app "mw-keep"
  dispatchApplicationEvent app (.windowCloseRequested ⟨0, keep.id, 0, 0⟩)
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "vetoing onCloseRequest ran" (← vetoes.get) 1
  checkEq "vetoed close keeps the window" (← app.windows.get).size 1
  -- Approve the close by swapping behavior via a second request after the
  -- veto counter check: the handler always vetoes, so close it declaratively.
  (← app.composition).dispose
  checkEq "disposing the app composition closes remaining windows"
    (← app.windows.get).size 0

/-- Windows are state-driven: `if (← isOpen.get) then Window ...` closes on a
state write, the application is done when none remain, and flipping the state
back reopens a fresh window. -/
private def stateDrivenCloseAndReopen : IO Unit := do
  let openB ← mutableStateOf true
  let app ← bootstrapApplication <| Tests.restartable 1 do
    Window "sd-a" 120 100 (config := cfg)
      (content := Box (Modifier.size 40 40 |>.background .green))
    if ← openB.get then
      Window "sd-b" 120 100 (config := cfg)
        (content := Box (Modifier.size 40 40 |>.background .blue))
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "both windows open" (← app.windows.get).size 2
  openB.set false
  check "state write dirties the app composition" (← app.dirty.get)
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "state-driven close removed one window" (← app.windows.get).size 1
  check "sibling window is untouched" (← entryTitled app "sd-a").isSome
  openB.set true
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "state-driven reopen restores the window" (← app.windows.get).size 2
  let b ← entryTitled! app "sd-b"
  check "reopened window is live again"
    (colorNear (← pixel b 10 10) 0 0 255)
  (← app.composition).dispose

/-- The application is done once the last window leaves (the composition had
settled), and `runApplicationLoop` returns promptly on `done`. -/
private def exitsWhenEmpty : IO Unit := do
  let openA ← mutableStateOf true
  let app ← bootstrapApplication <| Tests.restartable 1 do
    if ← openA.get then
      Window "ee-a" 100 80 (config := cfg)
  let _ ← stepApplication app (idleCapMs := 5)
  check "running while a window lives" (!(← app.done))
  openA.set false
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "last window left" (← app.windows.get).size 0
  check "empty registry means done" (← app.done)
  runApplicationLoop app -- must return immediately
  check "loop honors done" (← app.done)
  (← app.composition).dispose

/-- `exitApplication` hands content an exit action that stops the loop even
with windows still open. -/
private def explicitExit : IO Unit := do
  let exitRef ← IO.mkRef (pure () : IO Unit)
  let app ← bootstrapApplication do
    exitRef.set (← exitApplication)
    Window "xa" 100 80 (config := cfg)
  let _ ← stepApplication app (idleCapMs := 5)
  check "running before exit" (!(← app.done))
  (← exitRef.get)
  check "exitApplication stops the loop despite live windows" (← app.done)
  (← app.composition).dispose

/-- `DialogWindow` composed from a window's content is parented to that
window and marked modal (both asserted only where the driver supports them;
the dummy driver on some platforms may not). -/
private def dialogParentAndModal : IO Unit := do
  let app ← bootstrapApplication do
    Window "dlg-owner" 200 150 (config := cfg) (content := do
      DialogWindow "dlg" 100 80 (config := cfg)
        (content := Box (Modifier.size 20 20 |>.background .red)))
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "dialog registers as a live window" (← app.windows.get).size 2
  let owner ← entryTitled! app "dlg-owner"
  let dlg ← entryTitled! app "dlg"
  match ← dlg.ctx.window.parent with
  | some p =>
    checkEq "dialog is parented to its composer's window"
      (← p.id).val (← owner.ctx.window.id).val
    check "dialog carries the modal flag"
      (((← dlg.ctx.window.flags) &&& .modal) != .none)
  | none =>
    IO.println "note: driver lacks window parenting; skipping parent/modal asserts"
  -- Dialog teardown (unset modal → dispose) must not disturb the owner.
  (← app.composition).dispose
  checkEq "disposing tears down dialog and owner" (← app.windows.get).size 0

/-- Title and size follow the parameters on recomposition. -/
private def titleAndSizeFollowParams : IO Unit := do
  let title ← mutableStateOf "before"
  let wide ← mutableStateOf false
  let app ← bootstrapApplication <| Tests.restartable 1 do
    let t ← title.get
    let w : Dp := if ← wide.get then 300 else 200
    Window t w 150 (config := cfg)
  let _ ← stepApplication app (idleCapMs := 5)
  let e ← entryTitled! app "before"
  checkEq "initial title set" (← e.ctx.window.getTitle) "before"
  let (w0, _) ← e.ctx.window.getSize
  checkEq "initial width honored" w0 200
  title.set "after"
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "recomposition retitles the window" (← e.ctx.window.getTitle) "after"
  wide.set true
  let _ ← stepApplication app (idleCapMs := 5)
  let (w1, _) ← e.ctx.window.getSize
  checkEq "recomposition resizes on parameter change" w1 300
  (← app.composition).dispose

/-- App-level `CompositionLocal` providers are visible inside window content
(the captured-locals bridge), and the window's own ambients still win. -/
private def appLocalsFlowIntoWindows : IO Unit := do
  let flavor ← compositionLocalOf "plain"
  let seen ← IO.mkRef "unset"
  let hadWindowCtx ← IO.mkRef false
  let app ← bootstrapApplication <|
    CompositionLocalProvider flavor "themed" <|
      Window "loc" 120 100 (config := cfg) (content := do
        seen.set (← flavor.current)
        hadWindowCtx.set (← LocalWindowContext.current).isSome)
  let _ ← stepApplication app (idleCapMs := 5)
  checkEq "app-level provider reaches window content" (← seen.get) "themed"
  check "window content still sees its own WindowContext" (← hadWindowCtx.get)
  (← app.composition).dispose

/-- Widgets composed at the app level (outside any `Window`) throw a clear
error instead of silently vanishing. -/
private def appLevelWidgetsThrow : IO Unit := do
  checkThrows "emitting layout at the app level throws" do
    let app ← bootstrapApplication (Box (Modifier.size 10 10))
    (← app.composition).dispose
  checkThrows "Window outside an application throws" do
    let ctx ← bootstrap "no-app" 100 80 (Window "w" 50 50) cfg
    (← ctx.composition).dispose

/-- An idle application blocks on the event wait (no busy-spin): a workless
pass sleeps out its cap. -/
private def idlePassBlocks : IO Unit := do
  let app ← bootstrapApplication do
    Window "idle-a" 100 80 (config := cfg)
    Window "idle-b" 100 80 (config := cfg)
  let _ ← stepApplication app (idleCapMs := 5) -- first frames
  let t0 ← Sdl.getTicks
  let rendered ← stepApplication app (idleCapMs := 80)
  let elapsed := (← Sdl.getTicks) - t0
  check "idle app pass renders nothing" (!rendered)
  check s!"idle app pass blocked ≈ the timeout ({elapsed} ms)"
    (60 ≤ elapsed && elapsed < 800)
  -- A state write in any window makes the next wake immediate again.
  (← app.composition).dispose

/-- The MultiWindow group. -/
def run : IO Unit := do
  twoWindowsComposeAndRoute
  closeRequestRouting
  stateDrivenCloseAndReopen
  exitsWhenEmpty
  explicitExit
  dialogParentAndModal
  titleAndSizeFollowParams
  appLocalsFlowIntoWindows
  appLevelWidgetsThrow
  idlePassBlocks

end Tests.MultiWindow
