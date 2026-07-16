module

public import Compose.Runtime.Scheduler
public meta import Compose.Runtime.Scheduler
public import Compose.Runtime.Effects
public meta import Compose.Runtime.Effects
public import Compose.Runtime.Locals
public meta import Compose.Runtime.Locals

public section

namespace Compose

/-!
# LaunchedEffect (`Compose/Runtime/LaunchedEffect.lean`)

The coroutine-launching composition effects, plugging `UiTask`/`Scheduler`
into M1's deferred `RememberObserver` queues: launch on the deferred
`onRemembered` (after the composition applies successfully), cancel on the
deferred `onForgotten`. `Composer.dispatchEffects` runs forgets before
remembers, so on a key change the predecessor is cancelled *before* the
successor launches, and everything is cancelled when the group leaves the
composition — exactly `androidx.compose.runtime.LaunchedEffect`'s ordering.

**Ambient scheduler.** The scheduler travels as the `LocalScheduler`
CompositionLocal (the analog of Compose's ambient effect
`CoroutineContext`): `Compose.runApp` provides the window's scheduler at the
root, and each restart scope captures its locals, so effects resolve it even
on standalone re-runs — this is what made a local the natural fit for M1's
plumbing (no new composition-owned field needed). Tests provide their own
via `CompositionLocalProvider`.
-/

/-- The ambient `Scheduler` coroutine effects launch on; provided at the root
by the app shell (`none` outside one — using an effect there throws a clear
error). Static: the value is per-window and never changes, so reads are free
and re-provision is not tracked. The analog of the `CoroutineContext`
Compose's `Recomposer` hands to composition effects. -/
initialize LocalScheduler : CompositionLocal (Option Scheduler) ←
  return { id := ← freshId, defaultValue := none, isStatic := true,
           eq := fun _ _ => true }

/-- The ambient scheduler, for launching work tied to no particular
composable lifetime (prefer `rememberLaunchScope` for auto-cancellation).
Throws when no scheduler is provided (composition outside `runApp` without a
`LocalScheduler` provider). Mirrors reaching Compose's effect
`CoroutineContext`. -/
def rememberScheduler : Composable Scheduler := do
  match ← LocalScheduler.current with
  | some s => return s
  | none => throw (IO.userError
      "Compose: no ambient Scheduler — LaunchedEffect/rememberLaunchScope \
       need a LocalScheduler provider (runApp installs one)")

/-- Launch `block` as a coroutine when this call enters the composition, and
whenever `k` changes (`BEq`); the previous coroutine is cancelled first. The
coroutine is cancelled when the call leaves the composition. Launch/cancel
are deferred to successful application in Compose's order (forgets of removed
groups run before new launches). Mirrors
`androidx.compose.runtime.LaunchedEffect(key1) { … }`. -/
def LaunchedEffect [BEq κ] (k : κ) (block : UiTask Unit) : Composable Unit := do
  let sched ← rememberScheduler
  let _ ← rememberObservedKeyed k do
    let job ← IO.mkRef (none : Option Job)
    pure ((), { onRemembered := do job.set (some (← sched.launch block))
                onForgotten := do (← job.get).forM (·.cancel) })

/-- A launcher scoped to a composition position: every coroutine launched
through it is cancelled when the remembering call leaves the composition.
Mirrors the `CoroutineScope` returned by `rememberCoroutineScope`. -/
structure LaunchScope where
  /-- The underlying scheduler. -/
  scheduler : Scheduler
  /-- Jobs launched through this scope (cancelled together on dispose). -/
  jobs : IO.Ref (Array Job)
  /-- `false` once the scope left the composition. -/
  active : IO.Ref Bool

instance : Nonempty LaunchScope :=
  ⟨{ scheduler := Classical.choice inferInstance
     jobs := Classical.choice inferInstance
     active := Classical.choice inferInstance }⟩

namespace LaunchScope

/-- Launch `t` under this scope. After the scope left the composition the
coroutine is not started and an already-cancelled `Job` is returned (Compose:
launching in a cancelled scope). Mirrors `CoroutineScope.launch`. -/
def launch (ls : LaunchScope) (t : UiTask Unit) : IO Job := do
  if ← ls.active.get then
    let j ← ls.scheduler.launch t
    ls.jobs.modify (·.push j)
    return j
  else
    let tok ← CancelToken.create
    tok.cancel
    return ⟨tok⟩

end LaunchScope

/-- Remember a `LaunchScope` bound to this composition position: coroutines
launched through it (from event handlers, typically) are cancelled when the
call leaves the composition. Mirrors
`androidx.compose.runtime.rememberCoroutineScope`. -/
def rememberLaunchScope : Composable LaunchScope := do
  let sched ← rememberScheduler
  rememberObserved do
    let scope : LaunchScope :=
      { scheduler := sched, jobs := ← IO.mkRef #[], active := ← IO.mkRef true }
    pure (scope, { onRemembered := pure ()
                   onForgotten := do
                     scope.active.set false
                     (← scope.jobs.get).forM (·.cancel) })

end Compose

end
