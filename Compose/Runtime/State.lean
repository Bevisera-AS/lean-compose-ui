namespace Compose

/-!
# Observable state

Snapshot-free read observation + targeted invalidation (documented deviation
from Compose's MVCC snapshots: everything runs on the main thread, so
single-threaded read tracking is observably equivalent).

A module-global *observer stack* records reads: pushing an observer while a
recomposition scope / measure pass / draw pass runs captures which states it
read. Only the **top** observer is notified for a given read, so an inner
observation (e.g. a `DerivedState` recomputing) owns its reads without leaking
them to the outer scope; the outer scope instead depends on the derived state
itself, mirroring Compose's derived-state dependency chains.

Registration is two-way (`ObservationRegistry`): each dependent records the
states its **latest** run read and unregisters them all before re-running,
matching `androidx.compose.runtime` scope-observation semantics; each state
holds the list of its dependents and invalidates them on a (policy-unequal)
write.
-/

/-- Unique identity for an observable state object. -/
structure StateId where
  id : Nat
  deriving BEq, Hashable, Repr

/-- Global counter backing `StateId` and `Invalidatable` freshness. -/
initialize freshIdCounter : IO.Ref Nat ← IO.mkRef 0

/-- Allocate a process-unique id. -/
def freshId : IO Nat := freshIdCounter.modifyGet fun n => (n, n + 1)

/-- A dependent that can be told its inputs changed: a recompose scope, a
layout node's remeasure, a window redraw. This is the abstraction Compose
spreads across `RecomposeScopeImpl`/`SnapshotStateObserver` scopes; keeping it
open lets layout and draw passes reuse the observation machinery. -/
structure Invalidatable where
  /-- Unique id, used for two-way (de)registration. -/
  id : Nat
  /-- Mark the dependent dirty (never runs work synchronously beyond queueing). -/
  invalidate : IO Unit

/-- Handle describing a state being read, passed to read observers. Bundles
just enough capability for two-way dependency registration without exposing
the state's value type. -/
structure ObservedHandle where
  stateId : StateId
  /-- Register a dependent (deduplicated by id) to invalidate on writes. -/
  addDependent : Invalidatable → IO Unit
  /-- Unregister the dependent with the given id. -/
  removeDependent : Nat → IO Unit

/-- The global ambient read-observer stack (see the module docstring).
Mirrors `androidx.compose.runtime.snapshots.Snapshot.observe` nesting. -/
initialize readObservers : IO.Ref (Array (ObservedHandle → IO Unit)) ← IO.mkRef #[]

/-- Notify the innermost (top) ambient read observer, if any, that a state is
being read. -/
def notifyRead (h : ObservedHandle) : IO Unit := do
  if let some obs := (← readObservers.get).back? then obs h

/-- Run `act` with `obs` pushed on the ambient read-observer stack. -/
def withReadObserver (obs : ObservedHandle → IO Unit) (act : IO α) : IO α := do
  readObservers.modify (·.push obs)
  try act finally readObservers.modify (·.pop)

/-- Two-way read-registration bookkeeping for one dependent: the states read
by its latest run, unregistered en masse before the next run. Mirrors the
per-scope observation sets of `androidx.compose.runtime.RecomposeScopeImpl`. -/
structure ObservationRegistry where
  dep : Invalidatable
  reads : IO.Ref (Array ObservedHandle)

namespace ObservationRegistry

/-- Fresh registry for the given dependent. -/
def create (dep : Invalidatable) : IO ObservationRegistry :=
  return { dep, reads := ← IO.mkRef #[] }

/-- Unregister this dependent from every state its latest run read. -/
def clear (r : ObservationRegistry) : IO Unit := do
  let hs ← r.reads.modifyGet fun hs => (hs, #[])
  hs.forM (·.removeDependent r.dep.id)

/-- Record one read: register the dependent with the state (idempotent) and
remember the handle for the next `clear`. -/
def record (r : ObservationRegistry) (h : ObservedHandle) : IO Unit := do
  if (← r.reads.get).any (·.stateId == h.stateId) then return
  h.addDependent r.dep
  r.reads.modify (·.push h)

/-- Run `act` observing all state reads on behalf of this registry, after
clearing the previous run's registrations (a dependent observes exactly the
states its latest run read). -/
def observe (r : ObservationRegistry) (act : IO α) : IO α := do
  r.clear
  withReadObserver r.record act

end ObservationRegistry

/-- An identity-carrying mutable cell whose reads are observable and whose
writes invalidate dependents. Mirrors `androidx.compose.runtime.MutableState`. -/
structure MutableState (α : Type) where
  id : StateId
  cell : IO.Ref α
  /-- Write-skip policy: a write equal to the current value (per this
  predicate) is a no-op. Mirrors `SnapshotMutationPolicy`. -/
  eq : α → α → Bool
  dependents : IO.Ref (Array Invalidatable)

instance [Nonempty α] : Nonempty (MutableState α) :=
  ⟨{ id := ⟨0⟩, cell := Classical.choice inferInstance,
     eq := fun _ _ => true, dependents := Classical.choice inferInstance }⟩

/-- Create a `MutableState` with an explicit equality policy. Prefer
`mutableStateOf`/`mutableStateOfAlwaysNotify`. -/
def mutableStateOfPolicy (eq : α → α → Bool) (init : α) : IO (MutableState α) :=
  return { id := ⟨← freshId⟩, cell := ← IO.mkRef init, eq,
           dependents := ← IO.mkRef #[] }

/-- Observable state with the structural-equality skip policy. Mirrors
`androidx.compose.runtime.mutableStateOf` (with `structuralEqualityPolicy`). -/
def mutableStateOf [BEq α] (init : α) : IO (MutableState α) :=
  mutableStateOfPolicy (· == ·) init

/-- Observable state that treats every write as a change. Mirrors
`mutableStateOf(init, neverEqualPolicy())`. -/
def mutableStateOfAlwaysNotify (init : α) : IO (MutableState α) :=
  mutableStateOfPolicy (fun _ _ => false) init

namespace MutableState

/-- The registration handle for this state's reads. -/
def handle (s : MutableState α) : ObservedHandle where
  stateId := s.id
  addDependent d :=
    s.dependents.modify fun ds => if ds.any (·.id == d.id) then ds else ds.push d
  removeDependent i := s.dependents.modify (·.filter (·.id != i))

/-- Read the value, registering the read with the ambient observer. Mirrors
`State<T>.value` reads inside composition/layout/draw. -/
def get (s : MutableState α) : IO α := do
  notifyRead s.handle
  s.cell.get

/-- Write the value: a no-op if equal per the state's policy, otherwise
invalidates all dependents. Mirrors `MutableState<T>.value =`. -/
def set (s : MutableState α) (v : α) : IO Unit := do
  let old ← s.cell.get
  if s.eq old v then return
  s.cell.set v
  (← s.dependents.get).forM (·.invalidate)

/-- Read-modify-write; the read is not registered with observers (only `get`
observes). Write-skip policy applies as in `set`. -/
def modify (s : MutableState α) (f : α → α) : IO Unit := do
  s.set (f (← s.cell.get))

end MutableState

/-- A read-only view of observable state: `get` registers the read with the
ambient observer exactly like `MutableState.get`, but the holder cannot
write. What `animate*AsState` and `Transition` hand out. Mirrors
`androidx.compose.runtime.State` (the read-only supertype of
`MutableState`). -/
structure State (α : Type) where
  /-- Read the current value, registering with the ambient observer. -/
  get : IO α

instance [Nonempty α] : Nonempty (State α) := ⟨⟨pure (Classical.choice ‹_›)⟩⟩

/-- This state, viewed read-only. Mirrors the `MutableState<T> : State<T>`
upcast. -/
def MutableState.asState (s : MutableState α) : State α := ⟨s.get⟩

/-- A cached computation over other states: dependents are invalidated only
when the recomputed value actually changes. Mirrors
`androidx.compose.runtime.derivedStateOf`. -/
structure DerivedState (α : Type) where
  id : StateId
  compute : IO α
  /-- `none` = never computed (dirty); eager recomputation on upstream writes
  keeps it fresh afterwards. -/
  cache : IO.Ref (Option α)
  eq : α → α → Bool
  dependents : IO.Ref (Array Invalidatable)
  /-- This derived state's own registration on the states `compute` reads. -/
  registry : ObservationRegistry

instance [Nonempty α] : Nonempty (DerivedState α) :=
  ⟨{ id := ⟨0⟩, compute := pure (Classical.choice inferInstance),
     cache := Classical.choice inferInstance, eq := fun _ _ => true,
     dependents := Classical.choice inferInstance,
     registry := { dep := ⟨0, pure ()⟩, reads := Classical.choice inferInstance } }⟩

/-- Create a derived state. When an upstream state changes, the value is
recomputed eagerly (re-registering its reads); dependents are invalidated
only if the recomputed value differs per `BEq`. Mirrors `derivedStateOf`. -/
def derivedStateOf [BEq α] (compute : IO α) : IO (DerivedState α) := do
  let cache ← IO.mkRef (none : Option α)
  let dependents ← IO.mkRef (#[] : Array Invalidatable)
  let invalidateRef ← IO.mkRef (pure () : IO Unit)
  let registry ← ObservationRegistry.create
    { id := ← freshId, invalidate := do (← invalidateRef.get) }
  let s : DerivedState α :=
    { id := ⟨← freshId⟩, compute, cache, eq := (· == ·), dependents, registry }
  invalidateRef.set do
    let newV ← registry.observe compute
    let old ← cache.get
    cache.set (some newV)
    unless old.any (· == newV) do
      (← dependents.get).forM (·.invalidate)
  return s

namespace DerivedState

/-- The registration handle for this derived state's reads. -/
def handle (s : DerivedState α) : ObservedHandle where
  stateId := s.id
  addDependent d :=
    s.dependents.modify fun ds => if ds.any (·.id == d.id) then ds else ds.push d
  removeDependent i := s.dependents.modify (·.filter (·.id != i))

/-- Read the derived value, registering the read with the ambient observer;
recomputes (and registers upstream reads) if dirty. -/
def get (s : DerivedState α) : IO α := do
  notifyRead s.handle
  match ← s.cache.get with
  | some v => return v
  | none =>
    let v ← s.registry.observe s.compute
    s.cache.set (some v)
    return v

end DerivedState

end Compose
