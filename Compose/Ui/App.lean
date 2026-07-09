import Compose.Ui.Window
import Compose.Ui.Layout
import Compose.Ui.Overlay
import Compose.Ui.Input.Router
import Compose.Ui.Draw.Scope

namespace Compose

/-!
# App shell (`Compose/Ui/App.lean`)

`Compose.runApp` — SDL init, window/renderer creation, and the dirty-driven,
power-friendly event loop from DESIGN.md:

1. Compute the wake deadline: `0` when a frame is pending (dirty or frame
   clock subscribed), else the scheduler's next timer deadline, else an
   idle cap; `waitEventTimeout` that long — never busy-spin when idle.
2. Translate and dispatch pending events (quit/close → quit; resize →
   remeasure; scale change → rebuild density + full invalidate; exposed →
   redraw; wake user events → nothing; everything else → `inputSink`).
3. Run due coroutines; tick the frame clock while it has subscribers.
4. If dirty: drain recompositions → remeasure with window-pixel constraints
   → clear + draw tree → present.

State writes anywhere schedule frames through the M5 invalidation hooks
(`Composition.setOnInvalidate`, `LayoutNode.setOnRequestRemeasure`) — the
loop never polls for dirtiness. `COMPOSE_MAX_FRAMES=<n>` exits successfully
after n loop passes (headless CI; passes rather than presented frames, so
static content terminates). The loop body is the testable
`Compose.step`; `Compose.bootstrap` builds a `WindowContext` without entering
the loop so tests can drive it manually.
-/

open Draw

/-- `runApp` configuration. Mirrors the window/dialog parameters of
Compose-for-Desktop's `application { Window(...) }` shell. -/
structure AppConfig where
  /-- Whether the user may resize the window. -/
  resizable : Bool := true
  /-- Request vsync-paced presentation (best effort; ignored where
  unsupported, e.g. dummy drivers). Under `Compose.application`, only one
  vsync-requesting window paces the shared loop (`electVSyncPacer`); the others
  present immediately to avoid serializing vblank waits. -/
  vsync : Bool := true
  /-- Every frame starts from this color. -/
  clearColor : Color := Color.white
  /-- Runs on `windowCloseRequested`; return `true` to quit (the default).
  Mirrors `onCloseRequest`. -/
  onCloseRequest : IO Bool := pure true
  /-- SDL renderer backend name (`none` = SDL's choice; tests pass
  `"software"` for stable readbacks). -/
  rendererName : Option String := none

/-- Milliseconds the idle loop sleeps per wait when nothing is scheduled (an
"∞-ish" cap: rewaiting is cheap and a finite bound is robust against missed
wakes). -/
def idleWaitMs : UInt32 := 1000

/-- Window size in **window coordinates** for a `Dp` extent, given the window's
SDL `displayScale` and `pixelDensity`.

SDL3's model: `sizeInPixels = size × pixelDensity`, and the `displayScale` this
framework already uses for its `Density` is `pixelDensity × OS content scale`.
Content is laid out at `displayScale`, so a `Dp` extent wants `dp × displayScale`
physical pixels; dividing by `pixelDensity` gives the window-coordinate extent
that yields exactly that. Identity on macOS/dummy (displayScale = pixelDensity,
e.g. 2/2 or 1/1) — where window coordinates *are* the layout unit — and a
scale-up on Windows, whose window coordinates are physical pixels (pixelDensity
1, displayScale = the OS scaling factor, e.g. 1.5/1 → ×1.5). A nonpositive
scale or density falls back to the density-1 estimate (`factor = 1`), so the
correction never fires on drivers that don't report metrics. -/
def windowCoordSize (dp : Dp) (displayScale pixelDensity : Float32) : Int32 :=
  let factor := if displayScale > 0 && pixelDensity > 0 then displayScale / pixelDensity else 1
  (dp.value * factor + 0.5).toInt32

-- macOS Retina (2/2) and the dummy driver (1/1): identity — no correction.
#guard windowCoordSize 400 2 2 == 400
#guard windowCoordSize 300 1 1 == 300
-- Windows at 150 % scaling (displayScale 1.5, pixelDensity 1): window coords
-- are pixels, so the extent scales up to keep layout and window in agreement.
#guard windowCoordSize 400 1.5 1 == 600
#guard windowCoordSize 300 1.5 1 == 450
-- Unreported metrics fall back to the density-1 estimate.
#guard windowCoordSize 400 0 0 == 400

/-- Build the per-window half of `bootstrap` on an *existing* scheduler and
wake event (`Compose.application` shares one pair across all its windows):
SDL window/renderer, text stack, root node, composition for `content`, and
the input pipeline, wiring both invalidation hooks to the window's
`needsFrame` flag — everything `step`/`renderFrame` need. `width`/`height`
are `Dp`; the window is created and kept at the matching window-coordinate
size (`windowCoordSize` — identity on macOS/dummy, scaled on Windows where
window coordinates are physical pixels). Main thread only. -/
def bootstrapWindow (scheduler : Scheduler) (wakeEvent : Sdl.EventType)
    (title : String) (width height : Dp) (content : Composable Unit)
    (config : AppConfig := {}) : IO WindowContext := do
  let flags :=
    (if config.resizable then Sdl.WindowFlags.resizable else .none) ||| .highPixelDensity
  let window ← Sdl.createWindow title
    (({} : Density).dpRoundToPx width) (({} : Density).dpRoundToPx height) flags
  -- Created at the density-1 estimate above; correct to the true window-
  -- coordinate size now that the display metrics are known. A no-op on
  -- macOS/dummy (displayScale = pixelDensity, so `getSize` already matches),
  -- a scale-up on Windows (window coordinates are physical pixels).
  let scale ← window.displayScale
  let pixelDensity ← window.pixelDensity
  let (ww, wh) := (windowCoordSize width scale pixelDensity,
                   windowCoordSize height scale pixelDensity)
  let (cw, ch) ← window.getSize
  unless cw == ww && ch == wh do window.setSize ww wh
  let renderer ← Sdl.createRenderer window config.rendererName
  if config.vsync then
    try renderer.setVSync 1 catch _ => pure ()
  -- Text stack: bundled fonts + renderer text engine (M7), shared per window.
  let textContext : TextContext :=
    { fontStore := ← FontStore.create
      textEngine := ← Sdl.Ttf.createRendererTextEngine renderer }
  let densityState ← mutableStateOf ({ density := if scale > 0 then scale else 1 } : Density)
  let ctx : WindowContext :=
    { window, renderer, densityState, scheduler, wakeEvent, textContext
      root := ← LayoutNode.create
      compositionCell := ← IO.mkRef none
      needsFrame := ← IO.mkRef true
      quitRequested := ← IO.mkRef false
      framesRendered := ← IO.mkRef 0
      inputSink := ← IO.mkRef fun _ => pure false
      overlays := ← mutableStateOfPolicy (fun _ _ => false) #[]
      keyHandlers := ← IO.mkRef #[]
      focusManager := ← IO.mkRef none
      modalFocusHook := ← IO.mkRef fun _ _ => pure () }
  -- Layout half of the invalidation wiring: any dirty walk reaching the root
  -- schedules a frame.
  ctx.root.setOnRequestRemeasure ctx.requestFrame
  -- M10: the root wrapper composes the overlay host right after the content,
  -- so popup/dialog layers become later (topmost) children of the root.
  let comp ← Composition.create (LayoutNode.applier ctx.root)
    (ctx.wrapContent (ctx.withOverlayHost content))
  -- Composition half: any scope invalidation (state write) schedules a frame.
  comp.setOnInvalidate ctx.requestFrame
  ctx.compositionCell.set (some comp)
  -- M6 input: translate SDL pointer/key/text events into the tree via the
  -- window's `inputSink` (tests may re-install with a recording cursor).
  -- M11 IME session: focus entering/leaving a text-input client (a node
  -- with `Modifier.onTextInput`) starts/stops SDL text input, so committed
  -- text and composition events flow only while a TextField is focused
  -- (DESIGN.md "Keyboard & IME"; the caret-rect `setTextInputArea` half
  -- lives in `Compose.Material.TextField`).
  let _ ← installInput ctx (onTextClientFocused := fun active => do
    if active then ctx.window.startTextInput
    else ctx.window.stopTextInput)
  return ctx

/-- SDL video init shared by `bootstrap` and `bootstrapApplication`: init the
subsystem and deliver the click that focuses an unfocused window instead of
swallowing it (SDL's default) — a button in a background window works on the
first click, like Compose Desktop. Normal priority, so the
`SDL_MOUSE_FOCUS_CLICKTHROUGH` env var still wins. -/
def initVideo : IO Unit := do
  Sdl.init .video
  Sdl.setHint Sdl.Hint.mouseFocusClickthrough "1"

/-- Create the SDL window/renderer, scheduler (woken by a registered SDL
user event), root node, and composition for `content`, wiring both
invalidation hooks to the window's `needsFrame` flag — everything `step`
needs, without entering the loop. `width`/`height` are `Dp` (sized in window
coordinates via `windowCoordSize`). Main thread only. -/
def bootstrap (title : String) (width height : Dp) (content : Composable Unit)
    (config : AppConfig := {}) : IO WindowContext := do
  initVideo
  let some wakeEvent ← Sdl.registerEvents 1
    | throw (IO.userError "Compose: SDL_RegisterEvents exhausted user event types")
  let scheduler ← Scheduler.create
    (wake := do let _ ← Sdl.pushUserEvent wakeEvent; pure ())
    (clock := Sdl.getTicksNS)
  bootstrapWindow scheduler wakeEvent title width height content config

/-- Dispatch one SDL event against the window (step 2 of the loop; exposed
for tests to inject synthetic events). -/
def dispatchEvent (ctx : WindowContext) (config : AppConfig) (event : Sdl.Event) : IO Unit := do
  match event with
  | .quit _ => ctx.requestQuit
  | .windowCloseRequested _ =>
    if ← config.onCloseRequest then ctx.requestQuit
  | .windowResized _ | .windowPixelSizeChanged _ =>
    -- New pixel constraints next frame; invalidate the root's measurement.
    ctx.root.markNeedsRemeasure
    ctx.requestFrame
  | .windowDisplayScaleChanged _ =>
    -- Rebuild the density and fully invalidate (providers recompose via the
    -- density state; cached measurements die via the density change).
    let scale ← ctx.window.displayScale
    ctx.densityState.set { density := if scale > 0 then scale else 1 }
    ctx.root.markNeedsRemeasure
    ctx.requestFrame
  | .windowExposed _ =>
    ctx.requestFrame
  | .user t _ =>
    if t == ctx.wakeEvent.val then
      pure () -- wake events exist only to end a wait
    else
      let _ ← (← ctx.inputSink.get) event
  | _ =>
    -- Input and everything else: M6's hook.
    let _ ← (← ctx.inputSink.get) event

/-- Render one frame (step 4): drain recompositions, remeasure the tree with
window-pixel constraints at the current density, clear, draw, present. The
`needsFrame` flag is consumed *before* draining so writes raised by effects
during the drain schedule the next frame instead of being lost. -/
def renderFrame (ctx : WindowContext) (config : AppConfig) : IO Unit := do
  ctx.needsFrame.set false
  (← ctx.composition).drain
  let density ← ctx.density
  let (pw, ph) ← ctx.window.getSizeInPixels
  -- Root constraints are the window pixels as maxima with zero minima —
  -- content wraps unless it fills (Compose's `ComposeScene` constraints).
  let _ ← ctx.root.remeasure { maxWidth := pw, maxHeight := ph } density
  let (r, g, b, a) := config.clearColor.toBytes
  ctx.renderer.setDrawColor r g b a
  ctx.renderer.clear
  DrawScope.run ctx.renderer density ctx.root.drawTree
  ctx.renderer.present
  ctx.framesRendered.modify (· + 1)

/-- Wait timeout for the next loop pass, in ms: `0` when a frame is pending
(dirty window or live frame clock), else time to the scheduler's next
deadline (rounded up), else `idleCapMs`. -/
def wakeTimeoutMs (ctx : WindowContext) (idleCapMs : UInt32 := idleWaitMs) : IO Int32 := do
  if (← ctx.needsFrame.get) || (← ctx.scheduler.hasFrameWork) then
    return 0
  let cap := idleCapMs.toUInt64
  match ← ctx.scheduler.nextDeadline with
  | none => return Int32.ofNat cap.toNat
  | some d =>
    let now ← Sdl.getTicksNS
    if d ≤ now then return 0
    return Int32.ofNat (min cap ((d - now) / 1_000_000 + 1)).toNat

/-- One pass of the event loop (steps 1–4 above): wait for events up to the
computed deadline, dispatch them all, run due coroutines, tick the frame
clock if subscribed, and render when dirty. Returns `true` iff a frame was
presented. `idleCapMs` bounds the idle sleep (tests shorten it). -/
def step (ctx : WindowContext) (config : AppConfig := {})
    (idleCapMs : UInt32 := idleWaitMs) : IO Bool := do
  -- 1+2: wait with deadline, then drain the whole queue.
  let timeout ← wakeTimeoutMs ctx idleCapMs
  if timeout == 0 then
    pure ()
  else if let some e ← Sdl.waitEventTimeout timeout then
    dispatchEvent ctx config e
  repeat
    match ← Sdl.pollEvent with
    | some e => dispatchEvent ctx config e
    | none => break
  if ← ctx.quitRequested.get then return false
  -- 3: coroutines due now; frame clock while subscribed.
  let now ← Sdl.getTicksNS
  ctx.scheduler.runDue now
  if ← ctx.scheduler.hasFrameWork then
    ctx.scheduler.tickFrame now
  -- 4: render when dirty.
  if ← ctx.needsFrame.get then
    renderFrame ctx config
    return true
  return false

/-- Idle-wait cap per pass while a pass budget is active, ms: capped passes
must terminate promptly even when the content is fully static (nothing wakes
the loop), so the headless smoke run never hangs on a settled screen. -/
def cappedIdleWaitMs : UInt32 := 5

/-- Run the loop until quit — or, when `maxPasses` is set, for that many
loop *passes* (then exit successfully; the headless CI mode). Counting
passes rather than presented frames guarantees termination for fully static
content — a settled screen presents nothing, but every pass still counts —
and while capped the idle wait shrinks to `cappedIdleWaitMs` so those idle
passes tick by promptly. -/
partial def runLoop (ctx : WindowContext) (config : AppConfig := {})
    (maxPasses : Option Nat := none) : IO Unit := do
  let idleCap := if maxPasses.isSome then cappedIdleWaitMs else idleWaitMs
  go maxPasses idleCap
where
  go (remaining : Option Nat) (idleCap : UInt32) : IO Unit := do
    if ← ctx.quitRequested.get then return
    if remaining == some 0 then return
    let _ ← step ctx config idleCap
    go (remaining.map (· - 1)) idleCap

/-- Loop passes to run before grabbing a screenshot — enough for effects,
layout, and the first idle frame to settle (animations get this much progress
and no more; a fixed count keeps capture deterministic). -/
def screenshotSettlePasses : Nat := 24

/-- Capture the app's rendered frame to `path` (BMP) instead of entering the
event loop — the README screenshot pipeline (`COMPOSE_SCREENSHOT=<path>`).
Boots the same composition on the **software renderer** (stable `readPixels`,
works under `SDL_VIDEO_DRIVER=dummy` so no window need be shown), settles for
`screenshotSettlePasses`, renders a final frame, and dumps the render target.
Convert BMP→PNG afterward (`sips -s format png in.bmp --out out.png`). Main
thread only. -/
def captureScreenshot (title : String) (width height : Dp)
    (content : Composable Unit) (config : AppConfig) (path : String) : IO Unit := do
  let capCfg := { config with rendererName := some Sdl.softwareRenderer, vsync := false }
  let ctx ← bootstrap title width height content capCfg
  for _ in [0:screenshotSettlePasses] do
    let _ ← step ctx capCfg cappedIdleWaitMs
  -- Force one last frame so the render target holds the settled content, then
  -- read it straight back (software target persists after `present`).
  ctx.requestFrame
  renderFrame ctx capCfg
  (← ctx.renderer.readPixels).saveBMP path
  (← ctx.composition).dispose

/-- Run a Compose application: create the window (`width`/`height` in `Dp`),
compose `content`, and drive the dirty-driven event loop until quit. Honors
`COMPOSE_MAX_FRAMES=<n>` (exit 0 after n loop passes — headless CI,
mirroring lean-sdl3's `SDL_LEAN_MAX_FRAMES`; passes, not presented frames,
so fully static demos terminate too) and `COMPOSE_SCREENSHOT=<path>` (dump
the settled frame to a BMP and exit — see `captureScreenshot`). Call from
`main` (main thread only).
Mirrors `androidx.compose.ui.window.singleWindowApplication`. -/
def runApp (title : String) (width height : Dp) (content : Composable Unit)
    (config : AppConfig := {}) : IO UInt32 := do
  if let some path ← IO.getEnv "COMPOSE_SCREENSHOT" then
    captureScreenshot title width height content config path
    return 0
  let ctx ← bootstrap title width height content config
  let maxPasses := (← IO.getEnv "COMPOSE_MAX_FRAMES").bind (·.toNat?)
  runLoop ctx config maxPasses
  (← ctx.composition).dispose
  return 0

end Compose
