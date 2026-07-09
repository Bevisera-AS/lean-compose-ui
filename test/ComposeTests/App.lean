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
  (← ctx.renderer.readPixels).readPixel x y

/-- First step renders the composition; probes hit content and clear color. -/
private def rendersComposition : IO Unit := do
  let ctx ← boot <| Box (Modifier.size 50 50 |>.background .red)
  check "app: bootstrap leaves the window dirty" (← ctx.needsFrame.get)
  check "app: first step renders" (← step ctx cfg)
  check "app: content pixel red" (colorNear (← pixel ctx 10 10) 255 0 0)
  let bg ← pixel ctx 120 100
  check s!"app: background is the clear color ({showColor bg})" (colorNear bg 255 255 255)

/-- A state write between steps redraws with changed pixels; a clean step in
between renders nothing (dirty-driven, wired through the invalidation
hooks — no polling). -/
private def stateWriteRedraws : IO Unit := do
  let color ← mutableStateOf Color.red
  let ctx ← boot <| Tests.restartable 1 do
    let c ← color.get
    Box (Modifier.size 50 50 |>.background c)
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
  let ctx ← boot (Box (Modifier.fillMaxSize |>.background .red))
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
  let ctx ← boot (Box (Modifier.size 10 10))
  dispatchEvent ctx cfg (.quit ⟨0⟩)
  check "quit: quit event requests exit" (← ctx.quitRequested.get)
  runLoop ctx cfg  -- must return promptly
  check "quit: loop exited" (← ctx.quitRequested.get)
  -- onCloseRequest decides for windowCloseRequested
  let ctx2 ← boot (Box (Modifier.size 10 10))
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
      Box (Modifier.size v 10 |>.background .red)
  runLoop ctx cfg (maxPasses := some 3)
  checkEq "max passes: busy loop renders every pass" (← ctx.framesRendered.get) 3
  check "max passes: frame clock drove the loop" ((← ticks.get) ≥ 1)
  -- Static content: nothing schedules frames after the first render, yet the
  -- capped loop must terminate (the smokePump-less smoke mode).
  let ctx2 ← boot (Box (Modifier.size 10 10 |>.background .red))
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

/-- An idle step (no dirty state, no timers, no frame work) blocks on the
event wait until the cap instead of spinning. Coarse bounds: at least most
of the timeout, well under ten times it. -/
private def idleStepBlocks : IO Unit := do
  let ctx ← boot (Box (Modifier.size 10 10 |>.background .red))
  let _ ← step ctx cfg  -- render; now fully idle
  let t0 ← Sdl.getTicks
  let rendered ← step ctx cfg (idleCapMs := 80)
  let elapsed := (← Sdl.getTicks) - t0
  check "idle: no frame from an idle step" (!rendered)
  check s!"idle: blocked ≈ the timeout ({elapsed} ms)" (60 ≤ elapsed && elapsed < 800)

/-- A scheduler timer bounds the wait: the loop wakes for the deadline, runs
the coroutine, and renders its state write. -/
private def timerWakesAndRenders : IO Unit := do
  let color ← mutableStateOf Color.red
  let ctx ← boot do
    LaunchedEffect 0 (block := do
      UiTask.delay 30
      color.set .blue)
    Tests.restartable 1 do
      let c ← color.get
      Box (Modifier.size 50 50 |>.background c)
  let _ ← step ctx cfg  -- initial render; LaunchedEffect queued → next step starts it
  let _ ← step ctx cfg (idleCapMs := 500)  -- starts the coroutine (parks 30 ms timer)
  -- Within a bounded number of waits the timer fires and repaints blue.
  let mut spins := 0
  while !(colorNear (← pixel ctx 10 10) 0 0 255) && spins < 50 do
    let _ ← step ctx cfg (idleCapMs := 500)
    spins := spins + 1
  check "timer: deadline woke the loop and repainted" (colorNear (← pixel ctx 10 10) 0 0 255)
  check "timer: took a few bounded steps, not a spin" (spins ≤ 5)

/-- The App group. -/
def run : IO Unit := do
  rendersComposition
  stateWriteRedraws
  resizeRemeasures
  windowSizeMatchesDensity
  quitHandling
  frameCapHonored
  idleStepBlocks
  timerWakesAndRenders

end Tests.App
