import Compose.Runtime.Composer

namespace Compose

/-!
# Composition-side effects

`RememberObserver` lifecycle plumbing plus the Compose effect primitives that
need no scheduler: `DisposableEffect` and `SideEffect`. Ordering matches
Compose exactly: all callbacks are deferred until the composition applies
successfully; forgotten callbacks of removed groups run depth-first, before
newly-remembered callbacks, before side effects (see
`Composer.dispatchEffects`).

`LaunchedEffect`/`UiTask` are milestone M5 (cooperative scheduler); they will
plug into the same deferred `onRemembered`/`onForgotten` queues (launch on
remember, cancel on forget).
-/

/-- Remember a value together with its lifecycle observer: `onRemembered`
runs after the composition applies; `onForgotten` runs (depth-first) when the
group is removed. Mirrors remembering a
`androidx.compose.runtime.RememberObserver`. -/
def rememberObserved [Nonempty α] (init : IO (α × RememberObserver)) : Composable α := fun c =>
  c.rememberObservedKeyed () init

/-- `rememberObserved` re-initialized when `k` changes: the old value is
forgotten (deferred, before the new value's `onRemembered`). -/
def rememberObservedKeyed [BEq κ] [Nonempty α] (k : κ) (init : IO (α × RememberObserver)) :
    Composable α := fun c =>
  c.rememberObservedKeyed k init

/-- Run `block` when entering the composition (or when `k` changes), and the
`IO Unit` it returns when leaving (or before re-running on a key change).
Both ends are deferred to successful application, in Compose's order.
Mirrors `androidx.compose.runtime.DisposableEffect`. -/
def DisposableEffect [BEq κ] (k : κ) (block : IO (IO Unit)) : Composable Unit := fun c => do
  let _ ← c.rememberObservedKeyed k do
    let disposer ← IO.mkRef (pure () : IO Unit)
    pure ((), { onRemembered := do disposer.set (← block)
                onForgotten := do (← disposer.get) })

/-- Schedule `block` to run after every successful application of a
composition this call is part of. Mirrors
`androidx.compose.runtime.SideEffect`. -/
def SideEffect (block : IO Unit) : Composable Unit := fun c =>
  c.pendingSideEffects.modify (·.push block)

/-- `derivedStateOf` remembered with lifecycle: the state is `dispose`d —
detached from its upstream states — when this call leaves the composition or
`k` changes. Plain `remember (derivedStateOf …)` would keep recomputing on
every upstream write forever. -/
def rememberDerivedKeyed [BEq κ] [BEq α] [Nonempty α] (k : κ) (compute : IO α) :
    Composable (DerivedState α) := fun c =>
  c.rememberObservedKeyed k do
    let d ← derivedStateOf compute
    pure (d, { onRemembered := pure (), onForgotten := d.dispose })

/-- Keyless `rememberDerivedKeyed`: one derived state per composition
position, disposed on leaving. Mirrors `remember { derivedStateOf { … } }`. -/
def rememberDerived [BEq α] [Nonempty α] (compute : IO α) : Composable (DerivedState α) :=
  rememberDerivedKeyed () compute

end Compose
