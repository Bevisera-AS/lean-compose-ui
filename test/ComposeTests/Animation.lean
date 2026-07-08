import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Animation test group (`test/ComposeTests/Animation.lean`)

M8's runtime animation behavior, fully deterministic: a fake-clock
`Scheduler` driven by manual `runDue`/`tickFrame` calls (no real sleeping).
Covers `Animatable` frame loops and interruption with velocity carry-over,
`animate*AsState` relaunch-on-target-change, `Transition` per-segment specs
and mid-flight retargeting, `InfiniteTransition` lifecycles, and
`AnimatedVisibility` keeping content composed until its exit finishes
(probed by layout-node counts). Pure spec/spring/easing math is `#guard`ed
in `Compose/Animation/*` instead.
-/

namespace Tests.Animation
open Compose Tests.Harness

/-- Milliseconds → the scheduler's nanosecond clock. -/
private def ms (n : UInt64) : UInt64 := n * 1_000_000

/-- A scheduler over a settable fake clock. -/
private def fakeSched : IO (Scheduler × IO.Ref UInt64) := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  return (s, clock)

/-- `|x − y| ≤ tol` for runtime float checks. -/
private def near (x y : Float32) (tol : Float32 := 0.01) : Bool := (x - y).abs ≤ tol

instance : ToString AnimationVector := ⟨fun v => toString v.values⟩

private def linTween (d : Nat) : AnimationSpec Float32 := .tween d 0 .linear

/-! ## Animatable -/

/-- A 300 ms linear tween advances per tick and lands on the exact target;
`isRunning` covers exactly the animation's lifetime; the frame-clock
subscription is dropped at the end. -/
private def tweenToTarget : IO Unit := do
  let (s, _) ← fakeSched
  let anim ← Animatable.create (0.0 : Float32) .float32
  checkEq "animatable: initial value" (← anim.peek) 0.0
  check "animatable: initially idle" (!(← anim.isRunning.cell.get))
  let _ ← s.launch (anim.animateTo 10.0 (linTween 300))
  s.runDue 0
  check "animatable: running after start" (← anim.isRunning.cell.get)
  checkEq "animatable: target recorded" (← anim.targetValue.cell.get) 10.0
  check "animatable: subscribed to the frame clock" (← s.hasFrameWork)
  s.tickFrame 0                     -- start-time frame, no write yet
  checkEq "animatable: no write on the start frame" (← anim.peek) 0.0
  s.tickFrame (ms 150)
  checkEq "animatable: linear midpoint" (← anim.peek) 5.0
  check "animatable: velocity ≈ span/duration"
    (near ((← anim.velocityVector).get 0) 33.333 (tol := 0.1))
  s.tickFrame (ms 300)
  checkEq "animatable: exact target at the end" (← anim.peek) 10.0
  check "animatable: idle after completion" (!(← anim.isRunning.cell.get))
  checkEq "animatable: velocity reset on completion" (← anim.velocityVector) (.v1 0)
  check "animatable: unsubscribed after completion" (!(← s.hasFrameWork))
  s.tickFrame (ms 400)
  checkEq "animatable: no writes after completion" (← anim.peek) 10.0

/-- A mid-flight `animateTo` starts from the current value AND the current
velocity: with a spring retarget the value keeps moving in the old direction
briefly (carried momentum, velocity sign preserved) before turning around. -/
private def interruptionCarriesVelocity : IO Unit := do
  let (s, _) ← fakeSched
  let anim ← Animatable.create (0.0 : Float32) .float32
  let _ ← s.launch (anim.animateTo 10.0 (linTween 300))
  s.runDue 0
  s.tickFrame 0
  s.tickFrame (ms 150)
  checkEq "interrupt: mid-flight value" (← anim.peek) 5.0
  let vBefore := (← anim.velocityVector).get 0
  check "interrupt: moving up before interruption" (vBefore > 30)
  -- Interrupt: reverse toward 0 with a critically-damped spring.
  let _ ← s.launch (anim.animateTo 0.0 (.spring 1.0 100 (some 0.01)))
  s.runDue (ms 150)
  checkEq "interrupt: velocity carried into the new animation"
    ((← anim.velocityVector).get 0) vBefore
  checkEq "interrupt: new target" (← anim.targetValue.cell.get) 0.0
  check "interrupt: still running" (← anim.isRunning.cell.get)
  s.tickFrame (ms 160)              -- old subscriber (stale generation) drops here
  checkEq "interrupt: stale loop writes nothing" (← anim.peek) 5.0
  s.tickFrame (ms 170)              -- 10 ms into the spring
  let v10 ← anim.peek
  check "interrupt: carried momentum overshoots upward first" (v10 > 5.0)
  check "interrupt: velocity sign continuous" ((← anim.velocityVector).get 0 > 0)
  -- Drive to completion (spring duration is finite via its threshold).
  let mut t := ms 170
  for _ in [0:2000] do
    if ← anim.isRunning.cell.get then
      t := t + ms 10
      s.tickFrame t
  checkEq "interrupt: settles exactly at the new target" (← anim.peek) 0.0
  check "interrupt: idle after settling" (!(← anim.isRunning.cell.get))

/-- `snapTo` cancels the in-flight animation and pins the value; `stop`
cancels keeping the current value. -/
private def snapAndStop : IO Unit := do
  let (s, _) ← fakeSched
  let anim ← Animatable.create (0.0 : Float32) .float32
  let _ ← s.launch (anim.animateTo 10.0 (linTween 300))
  s.runDue 0
  s.tickFrame 0
  s.tickFrame (ms 150)
  anim.snapTo 3.0
  checkEq "snapTo: value pinned" (← anim.peek) 3.0
  checkEq "snapTo: target pinned" (← anim.targetValue.cell.get) 3.0
  check "snapTo: idle" (!(← anim.isRunning.cell.get))
  checkEq "snapTo: velocity zeroed" (← anim.velocityVector) (.v1 0)
  s.tickFrame (ms 200)
  s.tickFrame (ms 300)
  checkEq "snapTo: cancelled loop never writes again" (← anim.peek) 3.0
  -- stop keeps the interrupted mid-flight value
  let _ ← s.launch (anim.animateTo 10.0 (linTween 100))
  s.runDue (ms 300)
  s.tickFrame (ms 300)
  s.tickFrame (ms 350)
  checkEq "stop: mid-flight value" (← anim.peek) 6.5   -- 3 + 7·0.5
  anim.stop
  check "stop: idle" (!(← anim.isRunning.cell.get))
  s.tickFrame (ms 400)
  checkEq "stop: value kept, no more writes" (← anim.peek) 6.5

/-- An underdamped spring overshoots the target and then settles within the
threshold; a critically-damped one never overshoots. -/
private def springOvershootAndCritical : IO Unit := do
  let (s, _) ← fakeSched
  -- underdamped
  let a ← Animatable.create (0.0 : Float32) .float32
  let _ ← s.launch (a.animateTo 10.0 (.spring Spring.dampingRatioHighBouncy 100 (some 0.01)))
  s.runDue 0
  s.tickFrame 0
  let mut t : UInt64 := 0
  let mut maxV : Float32 := 0
  for _ in [0:4000] do
    if ← a.isRunning.cell.get then
      t := t + ms 5
      s.tickFrame t
      maxV := max maxV (← a.peek)
  check "spring: underdamped overshoots the target" (maxV > 11.0)
  checkEq "spring: underdamped settles exactly on the target" (← a.peek) 10.0
  check "spring: underdamped finished" (!(← a.isRunning.cell.get))
  -- critically damped
  let b ← Animatable.create (0.0 : Float32) .float32
  let _ ← s.launch (b.animateTo 10.0 (.spring 1.0 100 (some 0.01)))
  s.runDue 0
  s.tickFrame 0
  t := 0
  let mut overshot := false
  for _ in [0:4000] do
    if ← b.isRunning.cell.get then
      t := t + ms 5
      s.tickFrame t
      if (← b.peek) > 10.0001 then overshot := true
  check "spring: critical never overshoots" (!overshot)
  checkEq "spring: critical lands on the target" (← b.peek) 10.0

/-! ## animate*AsState -/

/-- Target changes relaunch the coroutine (the old job is cancelled and
never writes again); the value animates from the interrupted position. -/
private def animateFloatAsStateLifecycle : IO Unit := do
  let t ← TestTree.create
  let (s, _) ← fakeSched
  let target ← mutableStateOf (0.0 : Float32)
  let cell ← IO.mkRef (none : Option (State Float32))
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      let tv ← target.get
      let st ← animateFloatAsState tv (linTween 100)
      SideEffect (cell.set (some st))
  let some st ← cell.get | throw (IO.userError "state not captured")
  s.runDue 0
  check "asState: no animation when already at the target" (!(← s.hasFrameWork))
  checkEq "asState: initial value" (← st.get) 0.0
  target.set 10.0
  comp.drain
  s.runDue 0
  check "asState: target change subscribes to frames" (← s.hasFrameWork)
  s.tickFrame 0
  s.tickFrame (ms 50)
  checkEq "asState: mid-flight value" (← st.get) 5.0
  -- retarget mid-flight: the first animation's job is cancelled
  target.set 0.0
  comp.drain
  s.runDue (ms 50)
  s.tickFrame (ms 60)     -- old subscriber dropped (cancelled job), new start frame
  checkEq "asState: cancelled job writes nothing" (← st.get) 5.0
  s.tickFrame (ms 110)    -- 50 ms into the new animation: 5 → 0 halfway
  checkEq "asState: relaunch animates from the interrupted value" (← st.get) 2.5
  s.tickFrame (ms 160)
  checkEq "asState: converges to the new target" (← st.get) 0.0
  check "asState: unsubscribed when done" (!(← s.hasFrameWork))

/-- The `Dp` and `Color` wrappers animate and land exactly on their typed
targets. -/
private def animateWrappersRoundtrip : IO Unit := do
  let t ← TestTree.create
  let (s, _) ← fakeSched
  let targetDp ← mutableStateOf (0 : Dp)
  let targetColor ← mutableStateOf Color.black
  let dpCell ← IO.mkRef (none : Option (State Dp))
  let colorCell ← IO.mkRef (none : Option (State Color))
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      let d ← targetDp.get
      let c ← targetColor.get
      let dst ← animateDpAsState d (.tween 100 0 .linear)
      let cst ← animateColorAsState c (.tween 100 0 .linear)
      SideEffect do
        dpCell.set (some dst)
        colorCell.set (some cst)
  let some dst ← dpCell.get | throw (IO.userError "dp state not captured")
  let some cst ← colorCell.get | throw (IO.userError "color state not captured")
  targetDp.set 8
  targetColor.set .red
  comp.drain
  s.runDue 0
  s.tickFrame 0
  s.tickFrame (ms 50)
  check "asState dp: midpoint" ((← dst.get) == (4 : Dp))
  let cMid ← cst.get
  check "asState color: mid red channel" (near cMid.r 0.5 (tol := 0.001))
  check "asState color: alpha stays opaque" (cMid.a == 1.0)
  s.tickFrame (ms 100)
  check "asState dp: exact target" ((← dst.get) == (8 : Dp))
  check "asState color: exact target" ((← cst.get) == Color.red)

/-! ## Transition -/

/-- Per-segment specs are honored, `currentState` follows Compose's
retargeting rule (segments start at the previous target), mid-flight
retargets are continuous, and `currentState`/`isRunning` update on settle. -/
private def transitionSegments : IO Unit := do
  let t ← TestTree.create
  let (s, _) ← fakeSched
  let targetSt ← mutableStateOf (0 : Nat)
  let trCell ← IO.mkRef (none : Option (Transition Nat))
  let vCell ← IO.mkRef (none : Option (State Float32))
  -- 0→1 animates in 100 ms, every other segment in 200 ms.
  let spec (seg : Transition.Segment Nat) : AnimationSpec Float32 :=
    if seg.isTransitioningTo 0 1 then linTween 100 else linTween 200
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      let tgt ← targetSt.get
      let tr ← updateTransition tgt
      let v ← tr.animateFloat spec (fun st => (st * 10).toFloat32)
      SideEffect do
        trCell.set (some tr)
        vCell.set (some v)
  let some tr ← trCell.get | throw (IO.userError "transition not captured")
  let some v ← vCell.get | throw (IO.userError "value not captured")
  s.runDue 0
  checkEq "transition: initial value" (← v.get) 0.0
  check "transition: initially idle" (!(← tr.isRunning.cell.get))
  -- 0 → 1 uses the 100 ms segment spec
  targetSt.set 1
  comp.drain
  check "transition: running right after retarget" (← tr.isRunning.cell.get)
  checkEq "transition: currentState lags" (← tr.currentState.cell.get) 0
  checkEq "transition: targetState updates" (← tr.targetState.cell.get) 1
  s.runDue 0
  s.tickFrame 0
  s.tickFrame (ms 50)
  checkEq "transition: 0→1 uses its 100 ms spec (midpoint)" (← v.get) 5.0
  s.tickFrame (ms 100)
  checkEq "transition: reaches the segment target" (← v.get) 10.0
  checkEq "transition: currentState updates when done" (← tr.currentState.cell.get) 1
  check "transition: idle when done" (!(← tr.isRunning.cell.get))
  -- 1 → 2 uses the 200 ms fallback spec
  targetSt.set 2
  comp.drain
  s.runDue (ms 100)
  s.tickFrame (ms 200)
  s.tickFrame (ms 300)
  checkEq "transition: 1→2 uses the 200 ms spec (midpoint)" (← v.get) 15.0
  -- retarget mid-flight back to 1: current jumps to the previous target,
  -- the value continues from where it is
  targetSt.set 1
  comp.drain
  checkEq "transition: retarget makes the previous target current"
    (← tr.currentState.cell.get) 2
  check "transition: running through the retarget" (← tr.isRunning.cell.get)
  s.runDue (ms 300)
  s.tickFrame (ms 310)
  checkEq "transition: no write from the cancelled segment" (← v.get) 15.0
  s.tickFrame (ms 410)
  checkEq "transition: retarget continues from the current value" (← v.get) 12.5
  s.tickFrame (ms 510)
  checkEq "transition: settles on the retargeted value" (← v.get) 10.0
  checkEq "transition: currentState settles" (← tr.currentState.cell.get) 1
  check "transition: idle after settling" (!(← tr.isRunning.cell.get))

/-- An infinite transition mirrors across reverse iterations, keeps running
across many ticks, and releases its frame subscription (back to baseline)
after leaving the composition. -/
private def infiniteTransitionLoop : IO Unit := do
  let t ← TestTree.create
  let (s, _) ← fakeSched
  let show' ← mutableStateOf true
  let vCell ← IO.mkRef (none : Option (State Float32))
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      if ← show'.get then
        withGroup 11 do
          let it ← rememberInfiniteTransition
          let v ← it.animateFloat 0 10 (.infiniteRepeatable (linTween 100) .reverse)
          SideEffect (vCell.set (some v))
      else
        withGroup 12 (pure ())
  let some v ← vCell.get | throw (IO.userError "value not captured")
  checkEq "infinite: baseline frame subscribers" (← s.frameSubs.get).size 0
  s.runDue 0
  check "infinite: subscribed while composed" (← s.hasFrameWork)
  s.tickFrame 0
  s.tickFrame (ms 80)
  checkEq "infinite: forward iteration" (← v.get) 8.0
  s.tickFrame (ms 120)
  checkEq "infinite: reverse iteration mirrors" (← v.get) 8.0
  s.tickFrame (ms 180)
  checkEq "infinite: reverse iteration continues down" (← v.get) 2.0
  s.tickFrame (ms 250)
  checkEq "infinite: third iteration forward again" (← v.get) 5.0
  check "infinite: still running after many ticks" (← s.hasFrameWork)
  -- leaving the composition cancels the loop and releases the subscription
  show'.set false
  comp.drain
  s.tickFrame (ms 260)   -- parked continuation is dropped (cancelled job)
  checkEq "infinite: value untouched after leaving" (← v.get) 5.0
  check "infinite: no frame work after leaving" (!(← s.hasFrameWork))
  checkEq "infinite: subscribers back to baseline" (← s.frameSubs.get).size 0

/-! ## AnimatedVisibility -/

private def visSpec : Option (AnimationSpec Float32) := some (.tween 100 0 .linear)

/-- Compose `content` under a fresh layout root with the scheduler provided. -/
private def composeVisibility (s : Scheduler) (visible : MutableState Bool) :
    IO (LayoutNode × Composition) := do
  let root ← LayoutNode.create
  let comp ← Composition.create (LayoutNode.applier root) <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      let vis ← visible.get
      AnimatedVisibility vis
        (enter := fadeIn ++ expandVertically (spec := visSpec))
        (exit := fadeOut ++ shrinkVertically (spec := visSpec))
        (content := Layout (Modifier.size 50 40) .leaf)
  return (root, comp)

private def rootChildCount (root : LayoutNode) : IO Nat :=
  return (← root.data).children.size

private def visNodeSize (root : LayoutNode) : IO IntSize := do
  let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
  (← root.child 0).size

private def visNodeAlpha (root : LayoutNode) : IO (Option Float32) := do
  let d ← (← root.child 0).data
  return d.modifier.elems.findSome? fun e =>
    match e with
    | .draw (.alpha a) => some a
    | _ => none

instance : ToString IntSize := ⟨fun s => s!"{s.width}x{s.height}"⟩

/-- Hiding keeps the content composed while the exit runs (alpha and size
fractions animate within bounds) and removes it exactly when the exit
completes. -/
private def visibilityExitKeepsContent : IO Unit := do
  let (s, _) ← fakeSched
  let visible ← mutableStateOf true
  let (root, comp) ← composeVisibility s visible
  s.runDue 0
  check "visibility: initially-visible content skips the enter animation"
    (!(← s.hasFrameWork))
  checkEq "visibility: content composed" (← rootChildCount root) 1
  checkEq "visibility: full size when shown" (← visNodeSize root) (⟨50, 40⟩ : IntSize)
  -- hide: exit runs for 100 ms; content stays composed throughout
  visible.set false
  comp.drain
  s.runDue 0
  checkEq "visibility: content still composed during exit" (← rootChildCount root) 1
  s.tickFrame 0
  s.tickFrame (ms 50)
  comp.drain
  checkEq "visibility: content composed mid-exit" (← rootChildCount root) 1
  checkEq "visibility: height shrinks with the fraction" (← visNodeSize root)
    (⟨50, 20⟩ : IntSize)
  checkEq "visibility: alpha fades with the fraction" (← visNodeAlpha root) (some 0.5)
  s.tickFrame (ms 100)
  comp.drain
  checkEq "visibility: content removed once the exit completes"
    (← rootChildCount root) 0
  check "visibility: no frame work after removal" (!(← s.hasFrameWork))

/-- Re-showing mid-exit reverses the animation from the current fraction
(content never leaves the composition). -/
private def visibilityReshowReverses : IO Unit := do
  let (s, _) ← fakeSched
  let visible ← mutableStateOf true
  let (root, comp) ← composeVisibility s visible
  s.runDue 0
  visible.set false
  comp.drain
  s.runDue 0
  s.tickFrame 0
  s.tickFrame (ms 50)          -- mid-exit: fraction 0.5
  comp.drain
  checkEq "reshow: mid-exit size" (← visNodeSize root) (⟨50, 20⟩ : IntSize)
  -- flip back: the exit coroutine is cancelled before it can remove content
  visible.set true
  comp.drain
  checkEq "reshow: content survives the flip" (← rootChildCount root) 1
  s.runDue (ms 50)
  s.tickFrame (ms 60)          -- enter start frame (exit's parked frame drops)
  comp.drain
  checkEq "reshow: fraction held across the handover" (← visNodeSize root)
    (⟨50, 20⟩ : IntSize)
  s.tickFrame (ms 110)         -- 50 ms into the enter: 0.5 → 0.75
  comp.drain
  checkEq "reshow: reverses upward from the interrupted fraction"
    (← visNodeSize root) (⟨50, 30⟩ : IntSize)
  checkEq "reshow: alpha recovers too" (← visNodeAlpha root) (some 0.75)
  s.tickFrame (ms 160)
  comp.drain
  checkEq "reshow: fully shown again" (← visNodeSize root) (⟨50, 40⟩ : IntSize)
  checkEq "reshow: content still composed" (← rootChildCount root) 1
  check "reshow: enter finished, no frame work" (!(← s.hasFrameWork))

/-- The Animation group. -/
def run : IO Unit := do
  tweenToTarget
  interruptionCarriesVelocity
  snapAndStop
  springOvershootAndCritical
  animateFloatAsStateLifecycle
  animateWrappersRoundtrip
  transitionSegments
  infiniteTransitionLoop
  visibilityExitKeepsContent
  visibilityReshowReverses

end Tests.Animation
