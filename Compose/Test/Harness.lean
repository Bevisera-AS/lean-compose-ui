module

public import Compose.Ui.App
public meta import Compose.Ui.App
public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Test.Semantics
public meta import Compose.Test.Semantics

public section

namespace Compose.Test

/-!
# Test harness (`Compose/Test/Harness.lean`)

`runComposeTest` — the `androidx.compose.ui.test.runComposeUiTest` analog,
Lean-shaped: it boots a real (headless-capable) window with the full
composition → layout → draw pipeline, composes the content under a
**fake-clock scheduler**, and runs a `TestM` body with complete control over
time. Nothing moves unless the test says so:

* `awaitIdle` drains recompositions, coroutine starts, and renders — without
  advancing the clock (Compose's `waitForIdle`).
* `advanceTimeBy` moves the fake clock in frame-sized steps, ticking the
  frame clock so animations progress deterministically
  (`mainClock.advanceTimeBy`).
* `settle` advances until no animation subscribes to the frame clock.

Input enters through `sendEvent` → `Compose.dispatchEvent` → the window's
`inputSink` → `InputManager.sdlEvent` — the exact production path — with
positions converted render→window so the router's window→render translation
round-trips. Run under dummy drivers:
`SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy`.
-/

/-- Everything a running UI test owns: the bootstrapped window, the
fake-clock scheduler its content composes under, and the input manager whose
focus state assertions consult. Mirrors the `ComposeUiTest` receiver. -/
structure UiTest where
  /-- The bootstrapped window (renderer, root node, composition, …). -/
  ctx : WindowContext
  /-- The `AppConfig` frames render under. -/
  config : AppConfig
  /-- The fake-clock scheduler driving content coroutines and animations. -/
  sched : Scheduler
  /-- The controlled clock, in nanoseconds (`sched` reads it). -/
  clockRef : IO.Ref UInt64
  /-- The window's input pipeline (its `FocusManager` backs focus
  assertions). -/
  input : InputManager

/-- The UI-test monad: `IO` with the ambient `UiTest`. -/
abbrev TestM := ReaderT UiTest IO

/-- Renderer/window config for tests: SDL backend on the software renderer
(stable `readPixels`, immune to a stray `COMPOSE_BACKEND` in the
environment), no vsync, white clear color. -/
def testConfig : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white
    backend := some .sdlRenderer }

/-- The ambient `UiTest` (escape hatch to the raw window/renderer for pixel
probes and window-state checks). -/
def uiTest : TestM UiTest := read

/-- The controlled clock's current time, nanoseconds. -/
def now : TestM UInt64 := do (← read).clockRef.get

/-- Render one frame if anything is dirty (recompose → remeasure → draw);
no-op otherwise. -/
def render : TestM Unit := do
  let t ← read
  if ← t.ctx.needsFrame.get then
    let _ ← Compose.step t.ctx t.config

/-- Wait until the UI is idle **without advancing the clock**: run due
coroutine work, render dirty frames, repeat until no frame is pending and
neither scheduler has immediately-runnable work. The window's own scheduler
(which the production app loop drives — framework coroutines above the
test-local provider run there, e.g. `backdropHost`'s blur animation) is
driven alongside the test scheduler, on the same fake clock. Pending
*timers* and frame subscribers do not count — drive those with
`advanceTimeBy`/`settle`. Mirrors `waitForIdle`. -/
def awaitIdle : TestM Unit := do
  let t ← read
  for _ in [0:1000] do
    t.sched.runDue (← t.clockRef.get)
    t.ctx.scheduler.runDue (← t.clockRef.get)
    if ← t.ctx.needsFrame.get then
      let _ ← Compose.step t.ctx t.config
    else if (← t.sched.nextDeadline) != some 0
        && (← t.ctx.scheduler.nextDeadline) != some 0 then
      return
  throw (IO.userError "awaitIdle: UI did not become idle within 1000 rounds \
                       (a coroutine keeps enqueueing work?)")

/-- Advance the controlled clock by `ms` milliseconds in `frameMs`-sized
steps, running due coroutines and ticking the frame clock at each step —
animations progress exactly as if that time had passed at a steady frame
rate. Ends idle. Mirrors `mainClock.advanceTimeBy`. -/
def advanceTimeBy (ms : UInt64) (frameMs : UInt64 := 8) : TestM Unit := do
  let t ← read
  let mut remaining := ms
  while remaining > 0 do
    let dt := min (max frameMs 1) remaining
    remaining := remaining - dt
    let nowNs := (← t.clockRef.get) + dt * 1_000_000
    t.clockRef.set nowNs
    t.sched.runDue nowNs
    t.sched.tickFrame nowNs
    t.ctx.scheduler.runDue nowNs
    t.ctx.scheduler.tickFrame nowNs
    render
  awaitIdle

/-- Advance by one (or `n`) frame(s) of `frameMs`. Mirrors
`mainClock.advanceTimeByFrame`. -/
def advanceFrames (n : Nat := 1) (frameMs : UInt64 := 16) : TestM Unit :=
  for _ in [0:n] do advanceTimeBy frameMs frameMs

/-- Advance time until no coroutine subscribes to the frame clock (all
finite animations done), capped at `capMs` of fake time — the cap is not an
error, so infinite animations (progress spinners, caret blink) just get
`capMs` of progress. The auto-advance analog of `mainClock.autoAdvance`. -/
def settle (capMs : UInt64 := 4000) (frameMs : UInt64 := 8) : TestM Unit := do
  awaitIdle
  let t ← read
  let mut spent : UInt64 := 0
  while ((← t.sched.hasFrameWork) || (← t.ctx.scheduler.hasFrameWork))
      && spent < capMs do
    spent := spent + frameMs
    advanceTimeBy frameMs frameMs
  render

/-- Read one rendered pixel (render coordinates) — for the rare test where
pixel output is itself the property under test. -/
def pixel (x y : Int32) : TestM Sdl.Color := do
  let t ← read
  (← (← t.ctx.sdlRenderer).readPixels).readPixel x y

/-! ## Event synthesis (the real input path) -/

/-- Dispatch one synthetic SDL event exactly as the app loop would
(`Compose.dispatchEvent` → `inputSink` → `InputManager.sdlEvent`). -/
def sendEvent (e : Sdl.Event) : TestM Unit := do
  let t ← read
  dispatchEvent t.ctx t.config e

/-- Map a render-coordinate point (semantics bounds live there) to window
coordinates (synthetic mouse events carry those). -/
private def toWindow (pos : Offset) : TestM (Float32 × Float32) := do
  (← (← read).ctx.sdlRenderer).coordinatesToWindow pos.x pos.y

/-- Synthesize a mouse press at `pos` (render coordinates). -/
def mouseDown (pos : Offset) (button : Sdl.MouseButton := .left)
    (clicks : UInt8 := 1) : TestM Unit := do
  let (x, y) ← toWindow pos
  sendEvent (.mouseButtonDown ⟨0, ⟨0⟩, ⟨0⟩, button, true, clicks, x, y⟩)

/-- Synthesize a mouse release at `pos` (render coordinates). -/
def mouseUp (pos : Offset) (button : Sdl.MouseButton := .left)
    (clicks : UInt8 := 1) : TestM Unit := do
  let (x, y) ← toWindow pos
  sendEvent (.mouseButtonUp ⟨0, ⟨0⟩, ⟨0⟩, button, false, clicks, x, y⟩)

/-- Synthesize a mouse move to `pos` (render coordinates). -/
def mouseMove (pos : Offset) : TestM Unit := do
  let (x, y) ← toWindow pos
  sendEvent (.mouseMotion ⟨0, ⟨0⟩, ⟨0⟩, .none, x, y, 0, 0⟩)

/-- Synthesize a wheel scroll at `pos` (render coordinates); `delta` is in
wheel ticks, positive `y` = away from the user. -/
def mouseWheel (pos : Offset) (delta : Offset) : TestM Unit := do
  let (x, y) ← toWindow pos
  sendEvent (.mouseWheel ⟨0, ⟨0⟩, ⟨0⟩, delta.x, delta.y, .normal, x, y,
    delta.x.toInt32, delta.y.toInt32⟩)

/-- Synthesize a key-down (`isRepeat` for held-key repeats). -/
def keyDown (key : Sdl.Keycode) (mods : Sdl.Keymod := .none)
    (isRepeat : Bool := false) : TestM Unit :=
  sendEvent (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, key, mods, 0, true, isRepeat⟩)

/-- Synthesize a key-up. -/
def keyUp (key : Sdl.Keycode) (mods : Sdl.Keymod := .none) : TestM Unit :=
  sendEvent (.keyUp ⟨0, ⟨0⟩, ⟨0⟩, .unknown, key, mods, 0, false, false⟩)

/-- Synthesize a committed-text (IME commit / plain typing) event. -/
def textInput (text : String) : TestM Unit :=
  sendEvent (.textInput ⟨0, ⟨0⟩, text⟩)

/-- Synthesize an IME composition (`textEditing`) event (codepoint-indexed
cursor `start`/`length`, SDL semantics). -/
def textEditing (text : String) (start : Int32 := -1) (length : Int32 := 0) :
    TestM Unit :=
  sendEvent (.textEditing ⟨0, ⟨0⟩, text, start, length⟩)

/-! ## Semantics access -/

/-- The current semantics forest (merged unless `unmerged`), after waiting
for idle so pending recompositions and layout are reflected. -/
def semanticsNodes (unmerged : Bool := false) : TestM (Array SemanticsNode) := do
  awaitIdle
  semanticsForest (← read).ctx.root (merged := !unmerged)

/-- Dump the current (merged) semantics tree — appended to every failure
message; also handy for exploratory `IO.println`-debugging of a test. -/
def semanticsDump : TestM String := do
  return dumpForest (← semanticsNodes)

/-- The layout node currently holding keyboard focus, if any. -/
def focusedNode : TestM (Option LayoutNode) := do
  (← read).input.focus.focused

/-! ## The entry point -/

/-- Run a UI test: boot a headless-capable window (`testConfig`: software
renderer, no vsync), compose `content` under a **fake-clock scheduler** and
(by default) the light `MaterialTheme` (pass `theme := some myTheme` for a
custom one, `none` for no theme), bring the UI to its first idle frame,
run `body`, and dispose the composition. Time is fully controlled — see
`awaitIdle`/`advanceTimeBy`/`settle`. Mirrors
`androidx.compose.ui.test.runComposeUiTest` + `setContent`.

**Size your window for the content**: root constraints are the window pixels,
so content taller/wider than `width`/`height` gets cut by weight/fill layouts
— a too-small window silently collapses trailing rows to zero height and
their click targets vanish (the CRUD demo needed 540×460). The default is
480×360; pass explicit dimensions for bigger screens.

```lean
runComposeTest (counterApp) do
  click (.text "Increment")
  assertExists (.text "Count: 1")
```
-/
def runComposeTest (content : Composable Unit) (body : TestM Unit)
    (width : Dp := 480) (height : Dp := 360) (theme : Option Theme := some .light)
    (config : AppConfig := testConfig) :
    IO Unit := do
  let clockRef ← IO.mkRef (0 : UInt64)
  let sched ← Scheduler.create (clock := clockRef.get)
  let wrapped := match theme with
                 | some t => MaterialTheme content (theme := some t)
                 | none => content
  let ctx ← bootstrap "runComposeTest" width height
    (CompositionLocalProvider LocalScheduler (some sched) wrapped) config
    (clock := clockRef.get)
  -- Re-install the input pipeline to keep hold of the `InputManager` (focus
  -- assertions need its `FocusManager`); same wiring as `bootstrap`'s.
  let input ← installInput ctx (onTextClientFocused := fun active => do
    if active then ctx.window.startTextInput else ctx.window.stopTextInput)
  let t : UiTest := { ctx, config, sched, clockRef, input }
  try
    (do awaitIdle; body) |>.run t
  finally
    (← ctx.composition).dispose

end Compose.Test

end
