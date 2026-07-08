import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Scheduler test group (`test/ComposeTests/Scheduler.lean`)

Pure (SDL-free) tests for M5's cooperative scheduler and its composition
effects: `UiTask` delay ordering under a fake clock, structured cancellation,
background-`Task` await with push-wake, frame-clock subscription semantics,
`nextDeadline` math, nested launches, and the `LaunchedEffect` /
`rememberLaunchScope` lifecycle on the `TestApplier`.
-/

namespace Tests.Scheduler
open Compose Tests.Harness

/-- Milliseconds → the scheduler's nanosecond clock. -/
private def ms (n : UInt64) : UInt64 := n * 1_000_000

/-- A scheduler over a settable fake clock and a wake counter. -/
private def fakeSched : IO (Scheduler × IO.Ref UInt64 × IO.Ref Nat) := do
  let clock ← IO.mkRef (0 : UInt64)
  let wakes ← IO.mkRef (0 : Nat)
  let s ← Scheduler.create (wake := wakes.modify (· + 1)) (clock := clock.get)
  return (s, clock, wakes)

/-- Advance the fake clock and run everything due. -/
private def advance (s : Scheduler) (clock : IO.Ref UInt64) (toNs : UInt64) : IO Unit := do
  clock.set toNs
  s.runDue toNs

/-- Coroutine that logs `start`, then logs `tick` every 10 ms forever. -/
private partial def tickLoop (log : IO.Ref (Array String)) (tag : String) : UiTask Unit := do
  log.modify (·.push s!"start{tag}")
  loop
where loop : UiTask Unit := do
  UiTask.delay 10
  log.modify (·.push s!"tick{tag}")
  loop

/-- Two coroutines with interleaved deadlines resume in deadline order. -/
private def delayOrdering : IO Unit := do
  let (s, clock, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let push (x : String) : IO Unit := log.modify (·.push x)
  let _ ← s.launch do
    UiTask.delay 10; push "a10"
    UiTask.delay 20; push "a30"
  let _ ← s.launch do
    UiTask.delay 15; push "b15"
    UiTask.delay 5; push "b20"
  checkEq "delay: launch makes work immediate" (← s.nextDeadline) (some 0)
  s.runDue 0  -- start both; timers at 10 ms and 15 ms
  checkEq "delay: earliest deadline" (← s.nextDeadline) (some (ms 10))
  advance s clock (ms 10)
  checkEq "delay: first timer fired" (← log.get) #["a10"]
  checkEq "delay: next deadline after resume" (← s.nextDeadline) (some (ms 15))
  advance s clock (ms 20)
  checkEq "delay: second coroutine resumed" (← log.get) #["a10", "b15"]
  -- both remaining timers (b @25ms, a @30ms) come due at once: deadline order
  advance s clock (ms 40)
  checkEq "delay: batch fires in deadline order" (← log.get) #["a10", "b15", "b20", "a30"]
  checkEq "delay: all done, no deadline" (← s.nextDeadline) none

/-- Cancelling mid-delay drops the suspended continuation — no further
effects, even after the deadline passes. -/
private def cancelMidDelay : IO Unit := do
  let (s, clock, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let job ← s.launch (tickLoop log "A")
  s.runDue 0
  advance s clock (ms 10)
  checkEq "cancel: ran before cancellation" (← log.get) #["startA", "tickA"]
  job.cancel
  check "cancel: job reports cancelled" (← job.isCancelled)
  advance s clock (ms 100)
  checkEq "cancel: no effects after cancel" (← log.get) #["startA", "tickA"]

/-- Cancelling before the first `runDue` prevents the coroutine from
starting at all. -/
private def cancelBeforeStart : IO Unit := do
  let (s, clock, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let job ← s.launch (tickLoop log "B")
  job.cancel
  advance s clock (ms 50)
  checkEq "cancel: never started" (← log.get) (#[] : Array String)

/-- Awaiting a background `Task`: completion wakes the loop (push-wake from
the watcher thread) and the next `runDue` resumes the coroutine with the
task's value. -/
private def awaitTask : IO Unit := do
  let (s, _, wakes) ← fakeSched
  let got ← IO.mkRef (0 : Nat)
  let t ← IO.asTask (do IO.sleep 20; pure (42 : Nat))
  let _ ← s.launch do
    match ← UiTask.await t with
    | .ok v => got.set v
    | .error _ => pure ()
  s.runDue 0  -- starts the coroutine; it suspends on the await
  let wakesAtSuspend ← wakes.get
  checkEq "await: suspended without a value yet" (← got.get) 0
  let _ ← IO.wait t
  -- The watcher wakes from the task pool; give it a moment to run.
  let mut spins := 0
  while (← wakes.get) ≤ wakesAtSuspend && spins < 2000 do
    IO.sleep 1
    spins := spins + 1
  check "await: completion called wake" ((← wakes.get) > wakesAtSuspend)
  checkEq "await: finished task makes work immediate" (← s.nextDeadline) (some 0)
  s.runDue 0
  checkEq "await: resumed with the task's value" (← got.get) 42

/-- Awaiting an already-finished task resumes immediately (no wake needed). -/
private def awaitFinishedTask : IO Unit := do
  let (s, _, _) ← fakeSched
  let got ← IO.mkRef (0 : Nat)
  let _ ← s.launch do
    let v ← UiTask.await (Task.pure (7 : Nat))
    got.set v
  s.runDue 0
  checkEq "await: pre-finished task resumes inline" (← got.get) 7

/-- Frame subscribers run exactly once per tick; a coroutine looping on
`awaitFrame` re-subscribes for the next tick; the clock reports work only
while subscribers exist. -/
private def frameClock : IO Unit := do
  let (s, _, _) ← fakeSched
  let frames ← IO.mkRef (#[] : Array UInt64)
  let _ ← s.launch do
    for _ in [0:3] do
      let ns ← UiTask.awaitFrame
      frames.modify (·.push ns)
  check "frame: no subscribers before start" (!(← s.hasFrameWork))
  s.runDue 0
  check "frame: subscribed after start" (← s.hasFrameWork)
  s.tickFrame 100
  checkEq "frame: ran exactly once per tick" (← frames.get) #[100]
  check "frame: loop re-subscribed" (← s.hasFrameWork)
  s.tickFrame 200
  s.tickFrame 300
  checkEq "frame: one frame time per tick" (← frames.get) #[100, 200, 300]
  check "frame: unsubscribed after the loop ends" (!(← s.hasFrameWork))
  s.tickFrame 400
  checkEq "frame: tick without subscribers is a no-op" (← frames.get) #[100, 200, 300]

/-- `yield` defers the continuation to the *next* `runDue` (no starvation of
other queued work, no infinite drain). -/
private def yieldFairness : IO Unit := do
  let (s, _, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let _ ← s.launch do
    log.modify (·.push "1")
    UiTask.yield
    log.modify (·.push "2")
  s.runDue 0
  checkEq "yield: suspended at the yield" (← log.get) #["1"]
  checkEq "yield: queued work is immediate" (← s.nextDeadline) (some 0)
  s.runDue 0
  checkEq "yield: resumed on the next run" (← log.get) #["1", "2"]

/-- A coroutine can launch another; the nested launch starts on the next
`runDue`. -/
private def launchInsideCoroutine : IO Unit := do
  let (s, _, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let _ ← s.launch do
    log.modify (·.push "outer")
    let _ ← s.launch (liftM (log.modify (·.push "inner") : IO Unit))
    pure ()
  s.runDue 0
  checkEq "nested launch: queued, not run inline" (← log.get) #["outer"]
  checkEq "nested launch: deadline immediate" (← s.nextDeadline) (some 0)
  s.runDue 0
  checkEq "nested launch: ran on next run" (← log.get) #["outer", "inner"]

/-- `nextDeadline` arithmetic over timers and the run queue. -/
private def deadlineMath : IO Unit := do
  let (s, clock, _) ← fakeSched
  checkEq "deadline: idle scheduler has none" (← s.nextDeadline) none
  let _ ← s.launch (UiTask.delay 30)
  let _ ← s.launch (UiTask.delay 20)
  checkEq "deadline: pending starts are immediate" (← s.nextDeadline) (some 0)
  s.runDue 0
  checkEq "deadline: min of pending timers" (← s.nextDeadline) (some (ms 20))
  advance s clock (ms 20)
  checkEq "deadline: remaining timer" (← s.nextDeadline) (some (ms 30))
  advance s clock (ms 30)
  checkEq "deadline: drained back to none" (← s.nextDeadline) none

/-! ## LaunchedEffect / rememberLaunchScope -/

/-- `LaunchedEffect` launches on enter, relaunches on key change (the
predecessor is cancelled before the successor produces any effect), and is
cancelled when its group leaves the composition. -/
private def launchedEffectLifecycle : IO Unit := do
  let t ← TestTree.create
  let (s, clock, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let key ← mutableStateOf (0 : Nat)
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      let k ← key.get
      if k < 2 then
        withGroup 11 (LaunchedEffect k (tickLoop log s!"{k}"))
      else
        withGroup 12 (pure ())
  checkEq "LaunchedEffect: launch deferred to apply, started by runDue"
    (← log.get) (#[] : Array String)
  s.runDue 0
  checkEq "LaunchedEffect: launched on enter" (← log.get) #["start0"]
  advance s clock (ms 10)
  checkEq "LaunchedEffect: coroutine runs" (← log.get) #["start0", "tick0"]
  -- key change: predecessor cancelled (its 20 ms timer dies), successor starts
  key.set 1
  comp.drain
  s.runDue (ms 10)
  advance s clock (ms 40)
  checkEq "LaunchedEffect: relaunch on key change, predecessor cancelled"
    (← log.get) #["start0", "tick0", "start1", "tick1"]
  -- leaving the composition cancels the current coroutine
  key.set 2
  comp.drain
  advance s clock (ms 100)
  checkEq "LaunchedEffect: cancelled on leave-composition"
    (← log.get) #["start0", "tick0", "start1", "tick1"]

/-- Composing a `LaunchedEffect` without an ambient scheduler is a hard
error (clear misuse signal). -/
private def missingScheduler : IO Unit := do
  let t ← TestTree.create
  checkThrows "LaunchedEffect: throws without a LocalScheduler provider"
    (Composition.create t.applier (restartable 1 (LaunchedEffect 0 (pure ()))))

/-- `rememberLaunchScope` cancels every job launched through it when it
leaves the composition; later launches are stillborn. -/
private def launchScopeAutoCancel : IO Unit := do
  let t ← TestTree.create
  let (s, clock, _) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let scopeCell ← IO.mkRef (none : Option LaunchScope)
  let show' ← mutableStateOf true
  let comp ← Composition.create t.applier <|
    CompositionLocalProvider LocalScheduler (some s) <| restartable 1 do
      if ← show'.get then
        withGroup 11 do
          let ls ← rememberLaunchScope
          SideEffect (scopeCell.set (some ls))
      else
        withGroup 12 (pure ())
  let some ls ← scopeCell.get
    | throw (IO.userError "launch scope not captured")
  let j1 ← ls.launch (tickLoop log "S")
  s.runDue 0  -- start: logs startS, parks a 10 ms timer
  advance s clock (ms 10)
  checkEq "launch scope: job runs while composed" (← log.get) #["startS", "tickS"]
  check "launch scope: job live while composed" (!(← j1.isCancelled))
  show'.set false
  comp.drain
  advance s clock (ms 50)
  checkEq "launch scope: jobs cancelled on leave" (← log.get) #["startS", "tickS"]
  check "launch scope: job reports cancelled" (← j1.isCancelled)
  let j2 ← ls.launch (tickLoop log "T")
  advance s clock (ms 100)
  check "launch scope: launch after leave is stillborn" (← j2.isCancelled)
  checkEq "launch scope: stillborn job never ran" (← log.get) #["startS", "tickS"]

/-- The Scheduler group. -/
def run : IO Unit := do
  delayOrdering
  cancelMidDelay
  cancelBeforeStart
  awaitTask
  awaitFinishedTask
  frameClock
  yieldFairness
  launchInsideCoroutine
  deadlineMath
  launchedEffectLifecycle
  missingScheduler
  launchScopeAutoCancel

end Tests.Scheduler
