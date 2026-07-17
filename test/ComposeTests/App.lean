import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# App-shell test group (`test/ComposeTests/App.lean`)

Drives M5's `bootstrap`/`step`/`runLoop` headless (dummy video driver,
software renderer): first-frame pixels, state-write → dirty → re-render with
changed pixels (the invalidation→frame wiring end to end), clean steps render
nothing, synthetic resize events remeasure, quit dispatch, the
`COMPOSE_MAX_FRAMES`-style pass cap of `runLoop`, and idle blocking (a
workless step sleeps its wait out instead of spinning).
-/

namespace Tests.App
open Compose Tests.Harness

/-- Test config: software renderer for stable `readPixels`, no vsync. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

/-- Bootstrap a small test window. -/
private def boot (content : Composable Unit) : IO WindowContext :=
  bootstrap "compose-app-test" 200 150 content cfg

/-- Probe the renderer's current output at `(x, y)`. -/
private def pixel (ctx : WindowContext) (x y : Int32) : IO Sdl.Color := do
  (← (← ctx.sdlRenderer).readPixels).readPixel x y

/-- First step renders the composition; probes hit content and clear color. -/
private def rendersComposition : IO Unit := do
  let ctx ← boot <| Box (modifier := Modifier.size 50 50 |>.background .red)
  check "app: bootstrap leaves the window dirty" (← ctx.needsFrame.get)
  check "app: first step renders" (← step ctx cfg)
  check "app: content pixel red" (colorNear (← pixel ctx 10 10) 255 0 0)
  let bg ← pixel ctx 120 100
  check s!"app: background is the clear color ({showColor bg})" (colorNear bg 255 255 255)

/-- A state write between steps redraws with changed pixels; a clean step in
between renders nothing (dirty-driven, wired through the invalidation
hooks — no polling). -/
private def stateWriteRedraws : IO Unit := do
  let color ← MutableState.create Color.red
  let ctx ← boot <| Tests.restartable 1 do
    let c ← color.get
    Box (modifier := Modifier.size 50 50 |>.background c)
  let _ ← step ctx cfg
  check "app: initial color rendered" (colorNear (← pixel ctx 10 10) 255 0 0)
  check "app: clean step renders nothing" (!(← step ctx cfg (idleCapMs := 10)))
  color.set .blue
  check "app: state write marks the frame dirty" (← ctx.needsFrame.get)
  check "app: dirty step renders" (← step ctx cfg)
  check "app: pixels changed after the write" (colorNear (← pixel ctx 10 10) 0 0 255)

/-- A resize event remeasures: fill-parent content covers the new geometry. -/
private def resizeRemeasures : IO Unit := do
  let measures ← IO.mkRef (0 : Nat)
  let probedRoot : MeasurePolicy := fun ms m c => do
    measures.modify (· + 1)
    MeasurePolicy.root ms m c
  let ctx ← boot <| Layout (Modifier.fillMaxSize |>.background .green) probedRoot
  let _ ← step ctx cfg
  checkEq "resize: initial measure" (← measures.get) 1
  let (w0, _) ← ctx.window.getSizeInPixels
  check "resize: fill covers old edge" (colorNear (← pixel ctx (w0 - 2) 10) 0 255 0)
  check "resize: clean step stays cached" (!(← step ctx cfg (idleCapMs := 10)))
  checkEq "resize: no spurious measure" (← measures.get) 1
  -- Grow the window and inject the (dummy-driver-suppressed) resize event.
  ctx.window.setSize 300 200
  dispatchEvent ctx cfg (.windowResized ⟨0, ⟨0⟩, 300, 200⟩)
  check "resize: event marks the frame dirty" (← ctx.needsFrame.get)
  check "resize: step re-renders" (← step ctx cfg)
  checkEq "resize: remeasured once more" (← measures.get) 2
  let (w1, h1) ← ctx.window.getSizeInPixels
  check "resize: window pixels grew" (w1 > w0)
  check "resize: fill covers the new geometry"
    (colorNear (← pixel ctx (w1 - 2) (h1 - 2)) 0 255 0)

/-- Window sizing agrees with the layout density. On macOS/dummy
`displayScale = pixelDensity`, so `windowCoordSize` is the identity: the created
window keeps its requested `Dp` extent and no spurious `setSize` fires. The
Windows scale-up (window coordinates are physical pixels) can't run headless —
it is covered by `windowCoordSize`'s `#guard`s. -/
private def windowSizeMatchesDensity : IO Unit := do
  let ctx ← boot (Box (modifier := Modifier.fillMaxSize |>.background .red))
  let (w, h) ← ctx.window.getSize
  checkEq "size: window keeps requested width (identity correction)" w 200
  checkEq "size: window keeps requested height (identity correction)" h 150
  let scale ← ctx.window.displayScale
  let pd ← ctx.window.pixelDensity
  checkEq "size: windowCoordSize is identity under these metrics (w)"
    (windowCoordSize 200 scale pd) 200
  checkEq "size: windowCoordSize is identity under these metrics (h)"
    (windowCoordSize 150 scale pd) 150

/-- `quit`/`windowCloseRequested` dispatch sets the quit flag; `runLoop`
returns immediately. -/
private def quitHandling : IO Unit := do
  let ctx ← boot (Box (modifier := Modifier.size 10 10))
  dispatchEvent ctx cfg (.quit ⟨0⟩)
  check "quit: quit event requests exit" (← ctx.quitRequested.get)
  runLoop ctx cfg  -- must return promptly
  check "quit: loop exited" (← ctx.quitRequested.get)
  -- onCloseRequest decides for windowCloseRequested
  let ctx2 ← boot (Box (modifier := Modifier.size 10 10))
  dispatchEvent ctx2 { cfg with onCloseRequest := pure false } (.windowCloseRequested ⟨0, ⟨0⟩, 0, 0⟩)
  check "quit: vetoed close keeps running" (!(← ctx2.quitRequested.get))
  dispatchEvent ctx2 cfg (.windowCloseRequested ⟨0, ⟨0⟩, 0, 0⟩)
  check "quit: default close quits" (← ctx2.quitRequested.get)

/-- `runLoop` with a pass cap exits after exactly that many loop passes (the
`COMPOSE_MAX_FRAMES` mechanism): an animating window presents one frame per
pass, and a fully static one still terminates (idle passes count too). -/
private partial def frameCapHonored : IO Unit := do
  let ticks ← IO.mkRef (0 : Nat)
  let ctx ← boot do
    let w ← remember (mutableStateOf (10 : Dp))
    LaunchedEffect 0 (growForever ticks w)
    Tests.restartable 1 do
      let v ← w.get
      Box (modifier := Modifier.size v 10 |>.background .red)
  runLoop ctx cfg (maxPasses := some 3)
  checkEq "max passes: busy loop renders every pass" (← ctx.framesRendered.get) 3
  check "max passes: frame clock drove the loop" ((← ticks.get) ≥ 1)
  -- Static content: nothing schedules frames after the first render, yet the
  -- capped loop must terminate (the smokePump-less smoke mode).
  let ctx2 ← boot (Box (modifier := Modifier.size 10 10 |>.background .red))
  runLoop ctx2 cfg (maxPasses := some 5)
  checkEq "max passes: static content renders once" (← ctx2.framesRendered.get) 1
  check "max passes: static content terminates" (!(← ctx2.quitRequested.get))
where
  /-- Grow the width by 1 dp per frame, forever. -/
  growForever (ticks : IO.Ref Nat) (w : MutableState Dp) : UiTask Unit := do
    let _ ← UiTask.awaitFrame
    ticks.modify (· + 1)
    w.modify (fun d => ⟨d.value + 1⟩)
    growForever ticks w

/-- The live-resize watch callback renders synchronously — once per actual
size change (the several events of one drag tick dedupe via `lastSize`),
advancing the scheduler and frame clock as it goes — and only when armed
(loop parked in the pump), on a known window, not re-entrantly. Driven
directly with synthetic events: the dummy driver suppresses real resize
events, and the arming itself is exercised by every `runApp` under the
smoke script. -/
private partial def liveResizeWatchRenders : IO Unit := do
  let ctx ← boot (Box (modifier := Modifier.fillMaxSize |>.background .red))
  let _ ← step ctx cfg
  let f0 ← ctx.framesRendered.get
  let wid ← ctx.window.id
  let lookup : Sdl.WindowId → IO (Option (WindowContext × AppConfig)) := fun w =>
    return if w == wid then some (ctx, cfg) else none
  let armed ← IO.mkRef false
  let busy ← IO.mkRef false
  let last : IO.Ref (Option (Sdl.WindowId × Int32 × Int32)) ← IO.mkRef none
  let watchEvent := liveResizeWatchEvent lookup armed busy last
  let pixelChanged : Sdl.Event := .windowPixelSizeChanged ⟨0, wid, 300, 200⟩
  -- Unarmed (loop mid-drain or mid-render): must not render.
  watchEvent pixelChanged
  checkEq "watch: unarmed event does not render" (← ctx.framesRendered.get) f0
  armed.set true
  ctx.window.setSize 300 200
  -- `windowResized` precedes SDL's drawable-size update: never a trigger.
  watchEvent (.windowResized ⟨0, wid, 300, 200⟩)
  checkEq "watch: resized is ignored (stale drawable)" (← ctx.framesRendered.get) f0
  -- Armed pixel-size change: the callback remeasures and presents without
  -- any `step` — fill content covers the new geometry.
  watchEvent pixelChanged
  checkEq "watch: pixel-size change renders synchronously" (← ctx.framesRendered.get) (f0 + 1)
  check "watch: frame consumed (no pending dirty)" (!(← ctx.needsFrame.get))
  let (w1, h1) ← ctx.window.getSizeInPixels
  check "watch: fill covers the new geometry"
    (colorNear (← pixel ctx (w1 - 2) (h1 - 2)) 255 0 0)
  -- The rest of the drag tick's burst at the same size: deduped.
  watchEvent pixelChanged
  watchEvent (.windowExposed ⟨0, wid, 0, 0⟩)
  checkEq "watch: same-size burst renders once" (← ctx.framesRendered.get) (f0 + 1)
  -- An otherwise-dirtied window re-renders even at an unchanged size.
  ctx.requestFrame
  watchEvent (.windowExposed ⟨0, wid, 0, 0⟩)
  checkEq "watch: dirty window renders at unchanged size" (← ctx.framesRendered.get) (f0 + 2)
  -- Unknown window id: dropped.
  watchEvent (.windowPixelSizeChanged ⟨0, ⟨wid.val + 1⟩, 300, 200⟩)
  checkEq "watch: unknown window dropped" (← ctx.framesRendered.get) (f0 + 2)
  -- Busy (re-entered during its own render): dropped.
  busy.set true
  ctx.window.setSize 340 220
  watchEvent (.windowPixelSizeChanged ⟨0, wid, 340, 220⟩)
  busy.set false
  checkEq "watch: re-entrant call dropped" (← ctx.framesRendered.get) (f0 + 2)
  -- Non-resize events: ignored.
  watchEvent (.quit ⟨0⟩)
  checkEq "watch: unrelated event ignored" (← ctx.framesRendered.get) (f0 + 2)
  -- A size change advances the scheduler and frame clock (timers/animations
  -- progress mid-drag): an awaitFrame-looping coroutine ticks exactly once.
  let ticks ← IO.mkRef (0 : Nat)
  let ctx2 ← boot do
    LaunchedEffect 0 (tickForever ticks)
    Box (modifier := Modifier.fillMaxSize |>.background .red)
  let _ ← step ctx2 cfg  -- first render; queues the coroutine
  let _ ← step ctx2 cfg  -- starts it (parks on the frame clock)
  let wid2 ← ctx2.window.id
  let lookup2 : Sdl.WindowId → IO (Option (WindowContext × AppConfig)) := fun w =>
    return if w == wid2 then some (ctx2, cfg) else none
  let armed2 ← IO.mkRef true
  let busy2 ← IO.mkRef false
  let last2 : IO.Ref (Option (Sdl.WindowId × Int32 × Int32)) ← IO.mkRef none
  let t0 ← ticks.get
  ctx2.window.setSize 320 240
  liveResizeWatchEvent lookup2 armed2 busy2 last2 (.windowPixelSizeChanged ⟨0, wid2, 320, 240⟩)
  checkEq "watch: size change ticks the frame clock" (← ticks.get) (t0 + 1)
  -- `step` arms the watch only across its wait/poll phase.
  let watch ← installLiveResizeWatch lookup
  let _ ← step ctx cfg (idleCapMs := 5) (watch := some watch)
  check "watch: disarmed after a step" (!(← watch.armed.get))
  watch.remove
where
  /-- Bump `ticks` once per frame-clock tick, forever. -/
  tickForever (ticks : IO.Ref Nat) : UiTask Unit := do
    let _ ← UiTask.awaitFrame
    ticks.modify (· + 1)
    tickForever ticks

/-- An idle step (no dirty state, no timers, no frame work) blocks on the
event wait until the cap instead of spinning. Coarse bounds: at least most
of the timeout, well under ten times it. -/
private def idleStepBlocks : IO Unit := do
  let ctx ← boot (Box (modifier := Modifier.size 10 10 |>.background .red))
  let _ ← step ctx cfg  -- render; now fully idle
  let t0 ← Sdl.getTicks
  let rendered ← step ctx cfg (idleCapMs := 80)
  let elapsed := (← Sdl.getTicks) - t0
  check "idle: no frame from an idle step" (!rendered)
  check s!"idle: blocked ≈ the timeout ({elapsed} ms)" (60 ≤ elapsed && elapsed < 800)

/-- A scheduler timer bounds the wait: the loop wakes for the deadline, runs
the coroutine, and renders its state write. -/
private def timerWakesAndRenders : IO Unit := do
  let color ← MutableState.create Color.red
  let ctx ← boot do
    LaunchedEffect 0 (block := do
      UiTask.delay 30
      color.set .blue)
    Tests.restartable 1 do
      let c ← color.get
      Box (modifier := Modifier.size 50 50 |>.background c)
  let _ ← step ctx cfg  -- initial render; LaunchedEffect queued → next step starts it
  let _ ← step ctx cfg (idleCapMs := 500)  -- starts the coroutine (parks 30 ms timer)
  -- Within a bounded number of waits the timer fires and repaints blue.
  let mut spins := 0
  while !(colorNear (← pixel ctx 10 10) 0 0 255) && spins < 50 do
    let _ ← step ctx cfg (idleCapMs := 500)
    spins := spins + 1
  check "timer: deadline woke the loop and repainted" (colorNear (← pixel ctx 10 10) 0 0 255)
  check "timer: took a few bounded steps, not a spin" (spins ≤ 5)

/-- Lifecycle events: backgrounding pauses rendering (dirtiness is kept, not
lost), foregrounding repaints, `lowMemory` is safe mid-run, `terminating`
quits, and the `onLifecycle` hook observes each transition in order. -/
private def lifecyclePausesAndResumes : IO Unit := do
  let seen ← IO.mkRef (#[] : Array LifecycleEvent)
  let hookCfg := { cfg with onLifecycle := fun e => seen.modify (·.push e) }
  let color ← MutableState.create Color.red
  let ctx ← bootstrap "compose-app-test" 200 150
    (Tests.restartable 1 do
      let c ← color.get
      Box (modifier := Modifier.size 50 50 |>.background c))
    hookCfg
  let _ ← step ctx hookCfg
  check "lifecycle: initial render red" (colorNear (← pixel ctx 10 10) 255 0 0)
  dispatchEvent ctx hookCfg (.willEnterBackground ⟨0⟩)
  dispatchEvent ctx hookCfg (.didEnterBackground ⟨0⟩)
  check "lifecycle: backgrounded sets paused" (← ctx.paused.get)
  color.set .blue
  check "lifecycle: paused step renders nothing" (!(← step ctx hookCfg (idleCapMs := 10)))
  check "lifecycle: pixels unchanged while paused" (colorNear (← pixel ctx 10 10) 255 0 0)
  check "lifecycle: dirtiness kept for the resume" (← ctx.needsFrame.get)
  dispatchEvent ctx hookCfg (.lowMemory ⟨0⟩)
  dispatchEvent ctx hookCfg (.willEnterForeground ⟨0⟩)
  dispatchEvent ctx hookCfg (.didEnterForeground ⟨0⟩)
  check "lifecycle: foregrounded clears paused" (!(← ctx.paused.get))
  check "lifecycle: resume step repaints" (← step ctx hookCfg)
  check "lifecycle: deferred write now visible" (colorNear (← pixel ctx 10 10) 0 0 255)
  dispatchEvent ctx hookCfg (.terminating ⟨0⟩)
  check "lifecycle: terminating requests quit" (← ctx.quitRequested.get)
  check "lifecycle: hook saw the transitions in order"
    ((← seen.get) == #[.willEnterBackground, .didEnterBackground, .lowMemory,
                       .willEnterForeground, .didEnterForeground, .terminating])

/-- `onFirstFrame` fires exactly once, on the first *presented* frame — not
at bootstrap, and never again on later redraws. -/
private def firstFrameHookFires : IO Unit := do
  let fired ← IO.mkRef (0 : Nat)
  let color ← MutableState.create Color.red
  let ctx ← boot <| Tests.restartable 1 do
    let c ← color.get
    Box (modifier := Modifier.size 50 50 |>.background c)
  let hookCfg := { cfg with onFirstFrame := fired.modify (· + 1) }
  check "firstFrame: not fired at bootstrap" ((← fired.get) == 0)
  let _ ← step ctx hookCfg
  check "firstFrame: fired on the first presented frame" ((← fired.get) == 1)
  color.set .blue
  let _ ← step ctx hookCfg
  check "firstFrame: presented again" ((← ctx.framesRendered.get) == 2)
  check "firstFrame: hook stays fired-once" ((← fired.get) == 1)

/-- The IME-inset bridge end to end: a user event of the window's `imeEvent`
type publishes the keyboard inset (code = window px), `Modifier.imePadding`
shrinks content clear of it, and `screenKeyboardHidden` restores. -/
private def imeInsetPadding : IO Unit := do
  let ctx ← boot <| Tests.restartable 1 do
    Box (modifier := ← Modifier.imePadding) do
      Box (modifier := Modifier.fillMaxSize |>.background .green)
  let _ ← step ctx cfg
  check "ime: full bleed before the keyboard" (colorNear (← pixel ctx 10 148) 0 255 0)
  -- Keyboard opens 30 px tall.
  dispatchEvent ctx cfg (.user ctx.imeEvent.val ⟨0, ⟨0⟩, 30⟩)
  check "ime: the inset marks the frame dirty" (← ctx.needsFrame.get)
  let _ ← step ctx cfg
  check "ime: bottom padded clear of the keyboard"
    (colorNear (← pixel ctx 10 148) 255 255 255)
  check "ime: content sits above the keyboard" (colorNear (← pixel ctx 10 110) 0 255 0)
  -- The SDL hidden event zeroes the inset even without a bridge push.
  dispatchEvent ctx cfg (.screenKeyboardHidden ⟨0⟩)
  let _ ← step ctx cfg
  check "ime: hidden restores full bleed" (colorNear (← pixel ctx 10 148) 0 255 0)

/-- `imePadding` under a safe-area bottom inset pads only the excess (their
total is `max safe.bottom ime`, both measured from the window bottom). -/
private def imePaddingSafeAreaOverlap : IO Unit := do
  let ctx ← boot <| Tests.restartable 1 do
    -- NB the inner `do`: it keeps the `← Modifier.imePadding` read inside
    -- the provider (`<|` would lift the bind out to this outer block).
    CompositionLocalProvider LocalWindowInsets { bottom := 20 } do
      Box (modifier := ← Modifier.imePadding) do
        Box (modifier := Modifier.fillMaxSize |>.background .green)
  let _ ← step ctx cfg
  dispatchEvent ctx cfg (.user ctx.imeEvent.val ⟨0, ⟨0⟩, 30⟩)
  let _ ← step ctx cfg
  check "ime overlap: pads only the excess over the safe bottom"
    (colorNear (← pixel ctx 10 135) 0 255 0)
  check "ime overlap: the excess strip is clear"
    (colorNear (← pixel ctx 10 145) 255 255 255)
  -- A keyboard shorter than the safe bottom adds nothing.
  dispatchEvent ctx cfg (.user ctx.imeEvent.val ⟨0, ⟨0⟩, 15⟩)
  let _ ← step ctx cfg
  check "ime overlap: below the safe bottom nothing pads"
    (colorNear (← pixel ctx 10 148) 0 255 0)

/-- The bring-into-view trigger chain end to end: focus gain (through
`installInput`'s hook) scrolls a below-the-fold focusable into view, and an
IME inset change re-reveals it above the keyboard — both serviced by
`renderFrame` after remeasure, so the reveal sees the post-`imePadding`
layout. Animations run on the window's real-time scheduler here, so the
test steps with short sleeps under a bounded budget. -/
private def bringIntoViewOnFocusAndIme : IO Unit := do
  let sc ← ScrollState.create
  let ctx ← boot <| Tests.restartable 1 do
    Box (modifier := ← Modifier.imePadding) do
      Box (modifier := Modifier.fillMaxSize |>.verticalScroll sc) do
        Column do
          Box (modifier := Modifier.size 200 250)
          Box (modifier := Modifier.size 200 20 |>.focusable)
  let im ← installInput ctx
  let _ ← step ctx cfg
  checkEq "reveal e2e: content overflows" (← sc.maxValue) 120
  -- Tab focuses the offscreen box: the service is post-measure, next frame.
  check "reveal e2e: tab handled" (← im.keyEvent { key := .tab })
  check "reveal e2e: focus marks the frame dirty" (← ctx.needsFrame.get)
  let settle (want : Float32) : IO Unit := do
    for _ in [0:200] do
      if (← sc.value) == want then break
      IO.sleep 5
      let _ ← step ctx cfg
  settle 120
  checkEq "reveal e2e: focus scrolls the field into view" (← sc.value) 120
  -- The keyboard opens 30 px: the viewport shrinks and the field re-reveals.
  dispatchEvent ctx cfg (.user ctx.imeEvent.val ⟨0, ⟨0⟩, 30⟩)
  settle 150
  checkEq "reveal e2e: the IME inset re-reveals above the keyboard"
    (← sc.value) 150
  checkEq "reveal e2e: the range grew with the shrunk viewport"
    (← sc.maxValue) 150
  -- Hidden: the viewport grows back and the value re-clamps to the new
  -- max — the field stays at the bottom edge, nothing animates.
  dispatchEvent ctx cfg (.screenKeyboardHidden ⟨0⟩)
  let _ ← step ctx cfg
  let _ ← step ctx cfg
  checkEq "reveal e2e: dismissing the keyboard re-clamps into range"
    (← sc.value) 120

/-- `renderFrame` rides out transient backend-render exceptions (an Android
surface swap can make the Vulkan swapchain acquire throw): logs, re-arms the
frame, resets the streak on success — and still rethrows once the streak
hits `renderFailureLimit` (a genuinely dead device must crash loudly). -/
private def renderErrorResilience : IO Unit := do
  let ctx ← boot <| Box (modifier := Modifier.size 50 50 |>.background .red)
  let failing ← IO.mkRef true
  let real := ctx.backend
  let ctx := { ctx with
    backend := { real with
      render := fun clear list mayBlock => do
        if ← failing.get then
          throw (IO.userError "synthetic swapchain loss")
        real.render clear list mayBlock } }
  renderFrame ctx cfg
  check "resilience: first render failure survives" ((← ctx.renderFailures.get) == 1)
  check "resilience: a failed frame re-arms needsFrame" (← ctx.needsFrame.get)
  renderFrame ctx cfg
  check "resilience: the failure streak counts up" ((← ctx.renderFailures.get) == 2)
  failing.set false
  renderFrame ctx cfg
  check "resilience: success resets the streak" ((← ctx.renderFailures.get) == 0)
  check "resilience: the retried frame presented" ((← ctx.framesRendered.get) > 0)
  -- The rethrow path: a streak one short of the limit plus one more failure.
  failing.set true
  ctx.renderFailures.set (renderFailureLimit - 1)
  let threw ← try renderFrame ctx cfg; pure false catch _ => pure true
  check "resilience: a streak at the limit rethrows" threw

/-- The App group. -/
def run : IO Unit := do
  rendersComposition
  stateWriteRedraws
  firstFrameHookFires
  imeInsetPadding
  imePaddingSafeAreaOverlap
  bringIntoViewOnFocusAndIme
  resizeRemeasures
  windowSizeMatchesDensity
  quitHandling
  liveResizeWatchRenders
  frameCapHonored
  idleStepBlocks
  timerWakesAndRenders
  lifecyclePausesAndResumes
  renderErrorResilience

end Tests.App
