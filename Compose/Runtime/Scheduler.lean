import Compose.Runtime.State

namespace Compose

/-!
# Cooperative main-thread scheduler (`Compose/Runtime/Scheduler.lean`)

`UiTask` is a CPS-based cooperative coroutine monad — the Lean spelling of
the `suspend` blocks Compose runs on its main-thread dispatcher — and
`Scheduler` is the dispatcher + delay/frame-clock machinery
(`MonotonicFrameClock` + `Delay` of `kotlinx.coroutines` in one record).

**Threading.** Everything except `wake` runs on the main thread. The one
cross-thread edge is `UiTask.await`: a watcher hooked onto the awaited `Task`
calls `wake` from a task-pool thread when it completes so a sleeping event
loop gets out of `waitEventTimeout`. The app shell injects
`wake := pushUserEvent …` (SDL's `SDL_PushEvent` is thread-safe); this module
stays SDL-free.

**Cancellation** is structured but exception-free: every *suspension point*
(`delay`, `awaitFrame`, `await`, `yield`) checks the coroutine's
`CancelToken` both when suspending and when resuming, and a cancelled
coroutine simply never continues — Compose's Job-cancellation semantics
without unwinding across the FFI boundary. Code between suspension points
always runs to the next suspension. A cancelled coroutine's pending timer
stays queued and fires as a no-op (the scheduler may report its deadline —
one spurious wakeup, never a missed one). Because nothing unwinds, cleanup
that must not be skipped registers on the token: `CancelToken.onCancel` runs
it exactly once at cancellation (`UiTask.onCancel` scopes one to a task), and
`CancelToken.child` links `race` branches so parent cancellation reaches
them.

**Driving.** The owner (app loop or test) calls, per iteration:
`nextDeadline` (to size its sleep), `runDue now` (starts, timers, completed
awaits), and `tickFrame frameNs` when `hasFrameWork`. Work enqueued *during*
`runDue` (a `yield`, a nested `launch`) runs on the next call — `nextDeadline`
then reports `0`, so the loop comes right back without busy-spinning when
idle.
-/

/-- Cancellation flag shared between a coroutine and its `Job`, plus the
cleanup actions `cancel` runs exactly once (cancellation never unwinds, so
state resets and child-token links register here instead of in a `finally`).
Mirrors the cancelled state of a `kotlinx.coroutines.Job`. -/
structure CancelToken where
  /-- `true` once cancelled (never reset). -/
  flag : IO.Ref Bool
  /-- Pending `onCancel` cleanups, keyed for deregistration. -/
  actions : IO.Ref (Array (Nat × IO Unit))

namespace CancelToken

/-- A fresh, un-cancelled token. -/
def create : IO CancelToken :=
  return ⟨← IO.mkRef false, ← IO.mkRef #[]⟩

/-- Whether the token was cancelled. -/
def isCancelled (t : CancelToken) : IO Bool := t.flag.get

/-- Cancel: the owning coroutine stops at its next suspension check, and the
registered `onCancel` cleanups run. Only the first call does anything. -/
def cancel (t : CancelToken) : IO Unit := do
  unless ← t.flag.modifyGet fun f => (f, true) do
    (← t.actions.modifyGet fun a => (a, #[])).forM (·.2)

/-- Register `act` to run exactly once when the token is cancelled
(immediately when it already is). Returns a disposer: call it when the
guarded work completes, so registrations do not accumulate on long-lived
tokens (a gesture loop races once per press). -/
def onCancel (t : CancelToken) (act : IO Unit) : IO (IO Unit) := do
  if ← t.flag.get then
    act
    return pure ()
  let id ← freshId
  t.actions.modify (·.push (id, act))
  return t.actions.modify (·.filter (·.1 != id))

/-- A fresh token cancelled together with `t` but also cancellable on its
own — the parent→child half of structured cancellation (`race` branches).
Also returns the link's disposer, for when the child's work completes. -/
def child (t : CancelToken) : IO (CancelToken × IO Unit) := do
  let c ← create
  return (c, ← t.onCancel c.cancel)

end CancelToken

/-- Handle to a launched coroutine. Mirrors `kotlinx.coroutines.Job` (the
subset Compose effects need: cancellation). -/
structure Job where
  token : CancelToken

namespace Job

/-- Cancel the coroutine: it stops at its next suspension point; suspended
continuations are dropped when they come due. Mirrors `Job.cancel`. -/
def cancel (j : Job) : IO Unit := j.token.cancel

/-- Whether `cancel` was called. Mirrors `Job.isCancelled`. -/
def isCancelled (j : Job) : IO Bool := j.token.isCancelled

end Job

/-- The main-thread cooperative scheduler: run queue (starts, `yield`s),
timer queue (`delay` deadlines, nanos), frame-clock subscribers
(`awaitFrame`), and pending background-`Task` awaits. `wake` and `clock` are
injected by the owner (the app shell passes `pushUserEvent`/`getTicksNS`;
tests pass counters/fake clocks), keeping this module SDL-free. Mirrors the
dispatcher + `MonotonicFrameClock` Compose installs for effects. -/
structure Scheduler where
  /-- Wake a sleeping event loop. The *only* member that may be called off
  the main thread (`UiTask.await`'s completion watcher does). -/
  wake : IO Unit
  /-- Monotonic clock in nanoseconds, read at `delay` suspension. -/
  clock : IO UInt64
  /-- Continuations runnable now (launches, `yield`s). -/
  runQueue : IO.Ref (Array (IO Unit))
  /-- `(deadline nanos, resumption)` pairs, unordered. -/
  timers : IO.Ref (Array (UInt64 × IO Unit))
  /-- Current frame-clock subscribers; consumed (once each) by `tickFrame`. -/
  frameSubs : IO.Ref (Array (UInt64 → IO Unit))
  /-- Pending background awaits: `(finished?, resumption)`. Resumed by
  `runDue` after the completion watcher `wake`s the loop. -/
  taskWaits : IO.Ref (Array (BaseIO Bool × IO Unit))

instance : Nonempty Scheduler :=
  ⟨{ wake := pure (), clock := pure 0
     runQueue := Classical.choice inferInstance
     timers := Classical.choice inferInstance
     frameSubs := Classical.choice inferInstance
     taskWaits := Classical.choice inferInstance }⟩

namespace Scheduler

/-- Fresh scheduler. `wake` defaults to a no-op (fine for pure tests that
drive `runDue` directly); `clock` defaults to the Lean monotonic clock. -/
def create (wake : IO Unit := pure ())
    (clock : IO UInt64 := return (← IO.monoNanosNow).toUInt64) : IO Scheduler :=
  return { wake, clock
           runQueue := ← IO.mkRef #[]
           timers := ← IO.mkRef #[]
           frameSubs := ← IO.mkRef #[]
           taskWaits := ← IO.mkRef #[] }

end Scheduler

/-- A cooperative coroutine in continuation-passing style: given the
scheduler, the coroutine's cancellation token, and the continuation, either
run to completion (calling the continuation) or park the continuation on one
of the scheduler's queues. The Lean spelling of a `suspend () -> α` running
on Compose's main dispatcher. -/
structure UiTask (α : Type) where
  /-- Run under a scheduler and cancellation token, delivering the result to
  the continuation (possibly later, from a scheduler queue). -/
  run : Scheduler → CancelToken → (α → IO Unit) → IO Unit

instance : Monad UiTask where
  pure a := ⟨fun _ _ k => k a⟩
  bind t f := ⟨fun s tok k => t.run s tok fun a => (f a).run s tok k⟩
  map f t := ⟨fun s tok k => t.run s tok fun a => k (f a)⟩

/-- Plain `IO` runs inline on the main thread (not a suspension point);
exceptions propagate to whoever is driving the scheduler. -/
instance : MonadLift IO UiTask := ⟨fun io => ⟨fun _ _ k => io >>= k⟩⟩

namespace UiTask

/-- Wrap a resumption with the resume-side cancellation check: a continuation
coming due after `cancel` is dropped. -/
private def guarded (tok : CancelToken) (k : IO Unit) : IO Unit := do
  unless ← tok.isCancelled do k

/-- Suspend until the next `Scheduler.runDue` call (cooperative fairness —
work enqueued during a run executes on the *next* run). Mirrors
`kotlinx.coroutines.yield`. -/
protected def yield : UiTask Unit := ⟨fun s tok k => do
  unless ← tok.isCancelled do
    s.runQueue.modify (·.push (guarded tok (k ())))⟩

/-- Suspend for at least `ms` milliseconds of the scheduler's clock. Mirrors
`kotlinx.coroutines.delay`. -/
protected def delay (ms : UInt32) : UiTask Unit := ⟨fun s tok k => do
  unless ← tok.isCancelled do
    let now ← s.clock
    s.timers.modify (·.push (now + ms.toUInt64 * 1_000_000, guarded tok (k ())))⟩

/-- Suspend until the next frame-clock tick, resuming with the frame time in
nanoseconds. The loop ticks the clock only while subscribers exist, so an
idle UI burns no CPU. Mirrors
`androidx.compose.runtime.withFrameNanos { it }`. -/
protected def awaitFrame : UiTask UInt64 := ⟨fun s tok k => do
  unless ← tok.isCancelled do
    s.frameSubs.modify (·.push fun ns => guarded tok (k ns))⟩

/-- Suspend until the background `Task` completes, resuming with its value on
the main thread. A watcher mapped onto `t` calls `Scheduler.wake` from the
task pool when it finishes (push-wake: the sleeping event loop exits its
wait; its next `runDue` resumes this coroutine). An already-finished task
resumes immediately. Mirrors awaiting a `Deferred` from the main dispatcher. -/
protected def await (t : Task α) : UiTask α := ⟨fun s tok k => do
  unless ← tok.isCancelled do
    if ← IO.hasFinished t then
      k (← IO.wait t)
    else
      -- The value is fetched lazily inside the resumption (`IO.wait` on a
      -- finished task returns immediately; fetching it here would block).
      s.taskWaits.modify (·.push (IO.hasFinished t, guarded tok (do k (← IO.wait t))))
      let _ ← BaseIO.mapTask (fun _ => s.wake.catchExceptions fun _ => pure ()) t⟩

/-- Run `a` and `b` concurrently under this coroutine; complete with the first
result and cancel the loser (it stops at its next suspension point; a pending
loser timer fires as a no-op, per this module's cancellation contract). The
branches run under *child tokens* of the parent, so cancelling the parent
`Job` cancels both: a parked branch never resumes after the parent is
cancelled. The Lean spelling of `kotlinx.coroutines.selects.select`/`race` as
gesture detectors use it (e.g. long-press timeout vs. release). -/
protected def race (a b : UiTask α) : UiTask α := ⟨fun s tok k => do
  let winner ← IO.mkRef false
  let (ta, da) ← tok.child
  let (tb, db) ← tok.child
  let finish (loser : CancelToken) (v : α) : IO Unit := do
    unless ← winner.get do
      winner.set true
      da; db  -- the race is over: unlink both branches from the parent
      loser.cancel
      unless ← tok.isCancelled do k v
  a.run s ta fun v => finish tb v
  unless ← winner.get do
    b.run s tb fun v => finish ta v⟩

/-- Run `t` with `cleanup` registered on the coroutine's token: it runs
exactly once if the coroutine is cancelled before `t` completes — the
exception-free spelling of `try { t } finally { cleanup }` for cancellation
(a cancelled coroutine never resumes, so latched state must be reset from
the token). Completing `t` deregisters it. -/
protected def onCancel (cleanup : IO Unit) (t : UiTask α) : UiTask α :=
  ⟨fun s tok k => do
    let dispose ← tok.onCancel cleanup
    t.run s tok fun v => do dispose; k v⟩

end UiTask

namespace Scheduler

/-- Launch a coroutine: it is enqueued on the run queue (started by the next
`runDue`, matching Compose's dispatched `LaunchedEffect` start) and the loop
is woken. Returns the `Job` handle for cancellation. Main thread only.
Mirrors `CoroutineScope.launch`. -/
def launch (s : Scheduler) (t : UiTask Unit) : IO Job := do
  let tok ← CancelToken.create
  s.runQueue.modify (·.push (do unless ← tok.isCancelled do t.run s tok fun _ => pure ()))
  s.wake
  return ⟨tok⟩

/-- The earliest instant `runDue` would have work, or `none` when only a
`wake` (frame schedule, event, task completion) can create work: `0` when
the run queue is non-empty or a pending await already finished, otherwise
the earliest timer deadline. Frame subscribers are *not* deadlines — the
loop checks `hasFrameWork` separately. -/
def nextDeadline (s : Scheduler) : IO (Option UInt64) := do
  if !(← s.runQueue.get).isEmpty then return some 0
  for (finished, _) in (← s.taskWaits.get) do
    if ← finished then return some 0
  return (← s.timers.get).foldl (init := none) fun acc (d, _) =>
    match acc with
    | none => some d
    | some a => some (min a d)

/-- Run everything due at `nowNs`: the current run queue (snapshot — work
enqueued during the run waits for the next call), timers with
`deadline ≤ nowNs` in deadline order, and completed background awaits. -/
def runDue (s : Scheduler) (nowNs : UInt64) : IO Unit := do
  let ready ← s.runQueue.modifyGet fun q => (q, #[])
  ready.forM id
  let due ← s.timers.modifyGet fun ts =>
    (ts.filter (·.1 ≤ nowNs), ts.filter (nowNs < ·.1))
  (due.qsort (·.1 < ·.1)).forM (·.2)
  let waits ← s.taskWaits.modifyGet fun ws => (ws, #[])
  let mut still := #[]
  for w in waits do
    if ← w.1 then w.2 else still := still.push w
  s.taskWaits.modify (still ++ ·)

/-- Whether any coroutine is waiting on the frame clock (the loop renders
and ticks while this holds). Mirrors `MonotonicFrameClock.hasAwaiters`. -/
def hasFrameWork (s : Scheduler) : IO Bool :=
  return !(← s.frameSubs.get).isEmpty

/-- Tick the frame clock: every *current* subscriber runs exactly once with
`frameNs`; a coroutine that `awaitFrame`s again during the tick subscribes to
the *next* frame. Mirrors `BroadcastFrameClock.sendFrame`. -/
def tickFrame (s : Scheduler) (frameNs : UInt64) : IO Unit := do
  let subs ← s.frameSubs.modifyGet fun a => (a, #[])
  subs.forM (· frameNs)

end Scheduler

end Compose
