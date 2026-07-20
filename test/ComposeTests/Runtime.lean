import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Runtime test group

Composition/recomposition semantics on the `TestApplier`: positional
memoization, conditional insert/remove at exact indices, `keyed` reorder
moves, state-targeted invalidation, effect launch/dispose ordering,
CompositionLocal, and derived state.
-/

namespace Tests.Runtime
open Compose Tests.Harness

/-- `remember` returns the same value across recomposition; the initializer
runs exactly once. -/
def rememberSame : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let inits ← IO.mkRef (0 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← s.get
    let v ← remember (inits.modifyGet fun n => (n, n + 1))
    seen.modify (·.push v)
  s.set 1
  comp.drain
  checkEq "remember: initializer ran once" (← inits.get) 1
  checkEq "remember: same value across recomposition" (← seen.get) #[0, 0]

/-- `rememberKeyed` keeps its value while the key is `BEq`-equal and
re-initializes when it changes. -/
def rememberKeyedReinit : IO Unit := do
  let t ← TestTree.create
  let key ← MutableState.create "a"
  let inits ← IO.mkRef (0 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let k ← key.get
    let v ← rememberKeyed k (inits.modifyGet fun n => (n, n + 1))
    seen.modify (·.push v)
  key.set "a"
  comp.drain
  checkEq "rememberKeyed: equal key write is a no-op" (← seen.get) #[0]
  key.set "b"
  comp.drain
  checkEq "rememberKeyed: re-inits on key change" (← seen.get) #[0, 1]
  checkEq "rememberKeyed: initializer count" (← inits.get) 2

/-- Conditional content inserts/removes nodes at the correct indices between
siblings. -/
def conditional : IO Unit := do
  let t ← TestTree.create
  let flag ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    emitLabeled t "a"
    if ← flag.get then
      withGroup 11 (emitLabeled t "x")
    else
      withGroup 12 (pure ())
    emitLabeled t "b"
  checkEq "cond: initial tree" (← t.render) "(root a b)"
  let _ ← t.takeLog
  flag.set true
  comp.drain
  checkEq "cond: inserted between siblings" (← t.render) "(root a x b)"
  checkEq "cond: exactly one insert at index 1" (← t.takeLog) #["insert x at 1 in root"]
  flag.set false
  comp.drain
  checkEq "cond: removed again" (← t.render) "(root a b)"
  -- Like Compose's pending-group movement: the still-needed sibling node is
  -- relocated past the doomed group, whose nodes are removed at group end.
  checkEq "cond: relocate survivor, then remove" (← t.takeLog)
    #["move 1 from 2 to 1 in root", "remove 1 at 2 in root"]

/-- A conditional group emitting several nodes: range insert/remove with a
trailing sibling. -/
def multiNodeConditional : IO Unit := do
  let t ← TestTree.create
  let flag ← MutableState.create true
  let comp ← Composition.create t.applier <| restartable 1 do
    if ← flag.get then
      withGroup 11 do
        emitLabeled t "x"
        emitLabeled t "y"
    else
      withGroup 12 (pure ())
    emitLabeled t "z"
  checkEq "multi: initial tree" (← t.render) "(root x y z)"
  let _ ← t.takeLog
  flag.set false
  comp.drain
  checkEq "multi: both removed" (← t.render) "(root z)"
  checkEq "multi: survivor relocated, one range remove" (← t.takeLog)
    #["move 1 from 2 to 0 in root", "remove 2 at 1 in root"]
  flag.set true
  comp.drain
  checkEq "multi: re-inserted before z" (← t.render) "(root x y z)"
  checkEq "multi: two inserts at 0 and 1" (← t.takeLog)
    #["insert x at 0 in root", "insert y at 1 in root"]

/-- `keyed` list reorder produces applier `move`s and preserves per-key
remembered state; removal disposes the right group. -/
def keyedReorder : IO Unit := do
  let t ← TestTree.create
  let items ← MutableState.create ["a", "b", "c"]
  let ctr ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let xs ← items.get
    for x in xs do
      keyed x do
        let n ← remember (ctr.modifyGet fun n => (n, n + 1))
        emitText t s!"{x}{n}"
  checkEq "keyed: initial tree" (← t.render) "(root a0 b1 c2)"
  let _ ← t.takeLog
  items.set ["c", "a", "b"]
  comp.drain
  checkEq "keyed: reorder moved nodes, state preserved" (← t.render) "(root c2 a0 b1)"
  checkEq "keyed: exactly one move" (← t.takeLog) #["move 1 from 2 to 0 in root"]
  items.set ["c", "b"]
  comp.drain
  checkEq "keyed: removal keeps keyed state" (← t.render) "(root c2 b1)"
  checkEq "keyed: relocate then remove" (← t.takeLog)
    #["move 1 from 2 to 1 in root", "remove 1 at 2 in root"]
  checkEq "keyed: no re-initialization happened" (← ctr.get) 3

/-- Reordering keyed items that each emit two nodes moves the whole range. -/
def keyedMultiNodeMove : IO Unit := do
  let t ← TestTree.create
  let items ← MutableState.create ["a", "b"]
  let comp ← Composition.create t.applier <| restartable 1 do
    let xs ← items.get
    for x in xs do
      keyed x do
        emitLabeled t s!"{x}1"
        emitLabeled t s!"{x}2"
  checkEq "keyed2: initial tree" (← t.render) "(root a1 a2 b1 b2)"
  let _ ← t.takeLog
  items.set ["b", "a"]
  comp.drain
  checkEq "keyed2: range moved" (← t.render) "(root b1 b2 a1 a2)"
  checkEq "keyed2: one move of count 2" (← t.takeLog) #["move 2 from 2 to 0 in root"]

/-- A restart scope nested inside an emitted node re-runs standalone with the
correct base applier index and node parent. -/
def scopeInsideNode : IO Unit := do
  let t ← TestTree.create
  let flag ← MutableState.create false
  let comp ← Composition.create t.applier do
    emitLabeled t "box" do
      emitLabeled t "p"
      restartable 5 do
        if ← flag.get then
          withGroup 11 (emitLabeled t "q")
        else
          withGroup 12 (pure ())
      emitLabeled t "r"
  checkEq "nested: initial tree" (← t.render) "(root (box p r))"
  let _ ← t.takeLog
  flag.set true
  comp.drain
  checkEq "nested: inserted inside the node at base index" (← t.render) "(root (box p q r))"
  checkEq "nested: insert targeted the node parent" (← t.takeLog) #["insert q at 1 in box"]
  flag.set false
  comp.drain
  checkEq "nested: removed inside the node" (← t.render) "(root (box p r))"
  checkEq "nested: remove targeted the node parent" (← t.takeLog) #["remove 1 at 1 in box"]

/-- Scopes inside keyed items re-run standalone *after* a reorder: base
applier indices must reflect the new positions, including node-count deltas
propagated by earlier re-runs in the same drain. -/
def scopeRerunAfterReorder : IO Unit := do
  let t ← TestTree.create
  let items ← MutableState.create ["a", "b"]
  let flag ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    let xs ← items.get
    for x in xs do
      keyed x do
        emitLabeled t s!"{x}h"
        restartable 5 do
          if ← flag.get then
            withGroup 11 (emitLabeled t s!"{x}c")
          else
            withGroup 12 (pure ())
  checkEq "reorder+scope: initial tree" (← t.render) "(root ah bh)"
  items.set ["b", "a"]
  comp.drain
  checkEq "reorder+scope: reordered" (← t.render) "(root bh ah)"
  let _ ← t.takeLog
  flag.set true
  comp.drain
  checkEq "reorder+scope: standalone inserts at new positions"
    (← t.render) "(root bh bc ah ac)"
  checkEq "reorder+scope: insert indices account for earlier delta"
    (← t.takeLog) #["insert bc at 1 in root", "insert ac at 3 in root"]
  flag.set false
  comp.drain
  checkEq "reorder+scope: standalone removes at new positions"
    (← t.render) "(root bh ah)"
  checkEq "reorder+scope: remove indices account for earlier delta"
    (← t.takeLog) #["remove 1 at 1 in root", "remove 1 at 2 in root"]

/-- A state write re-runs exactly the scopes that read the state; `BEq`-equal
writes are no-ops. -/
def stateTargeting : IO Unit := do
  let t ← TestTree.create
  let sA ← MutableState.create (0 : Nat)
  let sB ← MutableState.create (0 : Nat)
  let rA ← IO.mkRef (0 : Nat)
  let rB ← IO.mkRef (0 : Nat)
  let rAB ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier do
    restartable 1 do
      let _ ← sA.get
      rA.modify (· + 1)
    restartable 2 do
      let _ ← sB.get
      rB.modify (· + 1)
    restartable 3 do
      let _ ← sA.get
      let _ ← sB.get
      rAB.modify (· + 1)
  checkEq "target: initial runs" ((← rA.get), (← rB.get), (← rAB.get)) (1, 1, 1)
  sA.set 1
  comp.drain
  checkEq "target: A write re-ran A readers only" ((← rA.get), (← rB.get), (← rAB.get)) (2, 1, 2)
  sB.set 7
  comp.drain
  checkEq "target: B write re-ran B readers only" ((← rA.get), (← rB.get), (← rAB.get)) (2, 2, 3)
  sA.set 1
  comp.drain
  checkEq "target: equal write is a no-op" ((← rA.get), (← rB.get), (← rAB.get)) (2, 2, 3)

/-- A scope observes exactly the states of its *latest* run: after the
condition flips, the no-longer-read state stops re-running the scope. -/
def latestRunReads : IO Unit := do
  let t ← TestTree.create
  let cond ← MutableState.create true
  let sX ← MutableState.create (0 : Nat)
  let runs ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    runs.modify (· + 1)
    if ← cond.get then
      withGroup 11 do let _ ← sX.get
    else
      withGroup 12 (pure ())
  checkEq "latest: initial run" (← runs.get) 1
  sX.set 1
  comp.drain
  checkEq "latest: read state re-runs" (← runs.get) 2
  cond.set false
  comp.drain
  checkEq "latest: condition flip re-runs" (← runs.get) 3
  sX.set 2
  comp.drain
  checkEq "latest: unread state no longer re-runs" (← runs.get) 3

/-- `mutableStateOfAlwaysNotify` invalidates on equal writes too. -/
def alwaysNotify : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.createAlwaysNotify (0 : Nat)
  let runs ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← s.get
    runs.modify (· + 1)
  s.set 0
  comp.drain
  checkEq "alwaysNotify: equal write re-runs" (← runs.get) 2

/-- A write during recomposition joins the same drain and converges. -/
def writeDuringRecomposition : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let runs ← IO.mkRef (0 : Nat)
  let _ ← Composition.create t.applier <| restartable 1 do
    runs.modify (· + 1)
    let v ← s.get
    if v < 3 then
      s.set (v + 1)
  checkEq "converge: settled value" (← s.get) 3
  checkEq "converge: ran until quiescent" (← runs.get) 4

/-- An unconditional self-write trips the iteration cap with a loud error. -/
def invalidationLoopDetected : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.createAlwaysNotify (0 : Nat)
  checkThrows "loop: iteration cap reported" <|
    Composition.create t.applier <| restartable 1 do
      s.set ((← s.get) + 1)

/-- A parent scope re-running also re-runs its invalid children in place; the
queue then skips them (no double runs). Valid children are skipped entirely,
with node indices intact across the skip. -/
def ancestorRerunsChild : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let rOuter ← IO.mkRef (0 : Nat)
  let rBoth ← IO.mkRef (0 : Nat)
  let rQuiet ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← s.get
    rOuter.modify (· + 1)
    emitLabeled t "a"
    restartable 2 do
      let _ ← s.get
      rBoth.modify (· + 1)
      emitLabeled t "i"
    restartable 3 do
      rQuiet.modify (· + 1)
      emitLabeled t "j"
    emitLabeled t "b"
  checkEq "ancestor: initial tree" (← t.render) "(root a i j b)"
  let _ ← t.takeLog
  s.set 1
  comp.drain
  checkEq "ancestor: outer and reading child ran once each"
    ((← rOuter.get), (← rBoth.get)) (2, 2)
  checkEq "ancestor: non-reading child skipped" (← rQuiet.get) 1
  checkEq "ancestor: tree unchanged" (← t.render) "(root a i j b)"
  checkEq "ancestor: no applier traffic" (← t.takeLog) (#[] : Array String)

/-- A helper `RememberObserver` that logs into `events`. -/
def logObserver (events : IO.Ref (Array String)) (name : String) :
    IO (Unit × RememberObserver) :=
  return ((), { onRemembered := events.modify (·.push s!"+{name}")
                onForgotten := events.modify (·.push s!"-{name}") })

/-- Removing nested groups forgets depth-first (children before parents),
before the replacement content's remembers. -/
def disposalOrdering : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let flag ← MutableState.create true
  let comp ← Composition.create t.applier <| restartable 1 do
    if ← flag.get then
      withGroup 11 do
        let _ ← rememberObserved (logObserver events "outer")
        withGroup 21 do
          let _ ← rememberObserved (logObserver events "inner")
    else
      withGroup 12 do
        let _ ← rememberObserved (logObserver events "new")
  checkEq "dispose: remembers in document order" (← events.get) #["+outer", "+inner"]
  events.set #[]
  flag.set false
  comp.drain
  checkEq "dispose: depth-first forgets before new remembers"
    (← events.get) #["-inner", "-outer", "+new"]

/-- `DisposableEffect`: runs on entry, disposes on key change (old disposal
before new launch) and on leaving the composition. -/
def disposableEffect : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let key ← MutableState.create "a"
  let alive ← MutableState.create true
  let comp ← Composition.create t.applier <| restartable 1 do
    if ← alive.get then
      withGroup 11 do
        let k ← key.get
        DisposableEffect k do
          events.modify (·.push s!"start {k}")
          pure (events.modify (·.push s!"stop {k}"))
    else
      withGroup 12 (pure ())
  checkEq "effect: launched after apply" (← events.get) #["start a"]
  events.set #[]
  key.set "b"
  comp.drain
  checkEq "effect: key change disposes old before new" (← events.get) #["stop a", "start b"]
  events.set #[]
  alive.set false
  comp.drain
  checkEq "effect: disposal on leave" (← events.get) #["stop b"]

/-- `SideEffect` runs after every successful application that executed it. -/
def sideEffect : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let s ← MutableState.create (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let v ← s.get
    SideEffect (events.modify (·.push s!"se {v}"))
  checkEq "sideEffect: after initial apply" (← events.get) #["se 0"]
  s.set 1
  comp.drain
  checkEq "sideEffect: after recomposition" (← events.get) #["se 0", "se 1"]
  s.set 1
  comp.drain
  checkEq "sideEffect: not on no-op writes" (← events.get) #["se 0", "se 1"]

/-- Dynamic `CompositionLocal`: a provider value change re-runs only the
readers; non-reading scopes in the subtree skip. -/
def localDynamic : IO Unit := do
  let t ← TestTree.create
  let l ← compositionLocalOf (0 : Nat)
  let s ← MutableState.create (1 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let rReader ← IO.mkRef (0 : Nat)
  let rOther ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let v ← s.get
    CompositionLocalProvider l v do
      restartable 2 do
        let cur ← l.current
        seen.modify (·.push cur)
        rReader.modify (· + 1)
      restartable 3 do
        rOther.modify (· + 1)
  checkEq "localDyn: initial read" (← seen.get) #[1]
  s.set 2
  comp.drain
  checkEq "localDyn: reader sees new value" (← seen.get) #[1, 2]
  checkEq "localDyn: reader re-ran" (← rReader.get) 2
  checkEq "localDyn: non-reader skipped" (← rOther.get) 1

/-- Static `CompositionLocal`: a provider value change recomposes the whole
provider subtree (readers and non-readers alike). -/
def localStatic : IO Unit := do
  let t ← TestTree.create
  let l ← staticCompositionLocalOf (0 : Nat)
  let s ← MutableState.create (1 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let rReader ← IO.mkRef (0 : Nat)
  let rOther ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let v ← s.get
    CompositionLocalProvider l v do
      restartable 2 do
        let cur ← l.current
        seen.modify (·.push cur)
        rReader.modify (· + 1)
      restartable 3 do
        rOther.modify (· + 1)
  checkEq "localStatic: initial read" (← seen.get) #[1]
  s.set 2
  comp.drain
  checkEq "localStatic: reader sees new value" (← seen.get) #[1, 2]
  checkEq "localStatic: whole subtree re-ran" ((← rReader.get), (← rOther.get)) (2, 2)

/-- Without a provider, `.current` yields the default; shadowing resolves to
the innermost provider. -/
def localDefaultAndShadowing : IO Unit := do
  let t ← TestTree.create
  let l ← compositionLocalOf (42 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let _ ← Composition.create t.applier do
    seen.modify (·.push (← l.current))
    CompositionLocalProvider l 1 do
      seen.modify (·.push (← l.current))
      CompositionLocalProvider l 2 do
        seen.modify (·.push (← l.current))
      seen.modify (·.push (← l.current))
  checkEq "local: default and shadowing" (← seen.get) #[42, 1, 2, 1]

/-- `derivedStateOf` caches its computation and invalidates dependents only
when the computed value changes. -/
def derivedState : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let computes ← IO.mkRef (0 : Nat)
  let d ← DerivedState.create do
    computes.modify (· + 1)
    return (← s.get) / 2
  let runs ← IO.mkRef (0 : Nat)
  let seen ← IO.mkRef (#[] : Array Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let v ← d.get
    seen.modify (·.push v)
    runs.modify (· + 1)
  checkEq "derived: computed once for first read" (← computes.get) 1
  let _ ← d.get
  checkEq "derived: cached read doesn't recompute" (← computes.get) 1
  s.set 1
  comp.drain
  checkEq "derived: upstream write recomputes" (← computes.get) 2
  checkEq "derived: equal result doesn't re-run readers" (← runs.get) 1
  s.set 4
  comp.drain
  checkEq "derived: changed result re-runs readers" (← runs.get) 2
  checkEq "derived: reader saw cached values" (← seen.get) #[0, 2]

/-- `setContent` recomposes against the existing tree; `dispose` forgets all
remembered observers and clears the applier. -/
def setContentAndDispose : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let comp ← Composition.create t.applier do
    let _ ← rememberObserved (logObserver events "x")
    emitLabeled t "a"
    emitLabeled t "b"
  checkEq "setContent: initial tree" (← t.render) "(root a b)"
  checkEq "setContent: initial remember" (← events.get) #["+x"]
  let _ ← t.takeLog
  comp.setContent do
    let _ ← rememberObserved (logObserver events "x")
    emitLabeled t "a"
  checkEq "setContent: leftover sibling removed" (← t.render) "(root a)"
  checkEq "setContent: one remove op" (← t.takeLog) #["remove 1 at 1 in root"]
  checkEq "setContent: remembered slot reused" (← events.get) #["+x"]
  comp.dispose
  checkEq "dispose: observer forgotten" (← events.get) #["+x", "-x"]
  checkEq "dispose: applier cleared" (← t.takeLog) #["clear"]
  checkEq "dispose: tree empty" (← t.render) "root"

/-- Changing the number of `remember`s inside one group (without a branch
group) is reported as a slot underflow instead of silent corruption. -/
def slotUnderflowReported : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← remember (pure (1 : Nat))
    if ← s.get then
      let _ ← remember (pure (2 : Nat))
  s.set true
  checkThrows "slots: underflow reported" comp.drain

/-- A forgotten remembered derived state detaches from its upstream states:
writes after removal no longer run `compute`. -/
def derivedStateUnsubscribes : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let alive ← MutableState.create true
  let computes ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    if ← alive.get then
      withGroup 11 do
        let d ← rememberDerived (α := Nat) do
          computes.modify (· + 1)
          return (← s.get) * 2
        let _ ← d.get
    else
      withGroup 12 (pure ())
  checkEq "derivedDispose: initial compute" (← computes.get) 1
  s.set 1
  comp.drain
  checkEq "derivedDispose: live upstream write recomputes" (← computes.get) 2
  alive.set false
  comp.drain
  let base ← computes.get
  s.set 2
  comp.drain
  checkEq "derivedDispose: forgotten derived stops recomputing" (← computes.get) base

/-- A key change replaces the remembered derived state; the old one is
disposed and stops tracking its upstreams. -/
def derivedKeyChangeDisposes : IO Unit := do
  let t ← TestTree.create
  let s ← MutableState.create (0 : Nat)
  let key ← MutableState.create "a"
  let computes ← IO.mkRef (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 do
    let k ← key.get
    let d ← rememberDerivedKeyed (α := Nat) k do
      computes.modify (· + 1)
      return (← s.get) * 2
    let _ ← d.get
  checkEq "derivedKey: initial compute" (← computes.get) 1
  key.set "b"
  comp.drain
  checkEq "derivedKey: new state computed once" (← computes.get) 2
  s.set 1
  comp.drain
  checkEq "derivedKey: only the live state recomputes" (← computes.get) 3

/-- Removing a subtree severs its internal reference cycles (Lean's runtime
is pure RC, no cycle collector): parent/scope/children/slots of every removed
group are cleared, so the subtree is actually freeable. -/
def removalSeversSubtree : IO Unit := do
  let t ← TestTree.create
  let flag ← MutableState.create true
  let captured ← IO.mkRef (none : Option Group)
  let capturedScope ← IO.mkRef (none : Option RecomposeScope)
  -- Raw combinators so the test can hold on to the group and its scope.
  let capture : Composable Unit := fun c => do
    let g ← c.startGroup 21 (isNode := false)
    captured.set (some g)
    let _ ← c.remember (IO.mkRef (0 : Nat))
    let scope ← c.startRestartGroup 22
    capturedScope.set (some scope)
    (emitLabeled t "x").run c
    c.endRestartGroup scope (pure ())
    c.endGroup
  let comp ← Composition.create t.applier <| restartable 1 do
    if ← flag.get then
      withGroup 11 capture
    else
      withGroup 12 (pure ())
  checkEq "sever: initial tree" (← t.render) "(root x)"
  flag.set false
  comp.drain
  checkEq "sever: node removed" (← t.render) "root"
  match ← captured.get, ← capturedScope.get with
  | some g, some scope =>
    let gd ← g.data
    check "sever: removed group's children cleared" gd.children.isEmpty
    check "sever: removed group's slots cleared" gd.slots.isEmpty
    check "sever: removed group's parent cleared" gd.parent.isNone
    let sgd ← scope.group.data
    check "sever: removed scope group's scope cleared" sgd.scope.isNone
    check "sever: removed scope group's parent cleared" sgd.parent.isNone
    check "sever: removed scope disposed" (← scope.disposed.get)
  | _, _ => check "sever: captured group and scope" false
  -- `dispose` severs the whole remaining tree the same way.
  flag.set true
  comp.drain
  comp.dispose
  match ← captured.get with
  | some g =>
    let gd ← g.data
    check "sever: disposed tree children cleared" gd.children.isEmpty
    check "sever: disposed tree parent cleared" gd.parent.isNone
  | none => check "sever: recaptured group" false

/-- A throw during initial composition propagates and rolls the runtime back
to a clean slate: no ghost nodes in the applier, no lifecycle callbacks from
the failed pass, and a fresh composition over the same applier works. -/
def throwOnInitialComposition : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  checkThrows "throw-init: error propagates" <|
    Composition.create t.applier do
      let _ ← rememberObserved (logObserver events "x")
      emitLabeled t "a"
      throw (IO.userError "boom")
  checkEq "throw-init: applier rolled back" (← t.render) "root"
  checkEq "throw-init: no lifecycle callbacks ran" (← events.get) (#[] : Array String)
  let comp ← Composition.create t.applier do
    let _ ← rememberObserved (logObserver events "x")
    emitLabeled t "a"
  checkEq "throw-init: retry composes cleanly" (← t.render) "(root a)"
  checkEq "throw-init: effects ran once" (← events.get) #["+x"]
  comp.dispose
  checkEq "throw-init: dispose balanced" (← events.get) #["+x", "-x"]

/-- A throw during recomposition propagates and unwinds the failed pass: the
applier and group tree stay consistent, the pass's pending effects are
abandoned (nothing launched, nothing double-run), and the scope recovers once
the offending state changes. -/
def throwDuringRecomposition : IO Unit := do
  let t ← TestTree.create
  let boom ← MutableState.create false
  let events ← IO.mkRef (#[] : Array String)
  let comp ← Composition.create t.applier <| restartable 1 do
    DisposableEffect "outer" do
      events.modify (·.push "start outer")
      pure (events.modify (·.push "stop outer"))
    emitLabeled t "a"
    if ← boom.get then
      withGroup 11 do
        DisposableEffect "inner" do
          events.modify (·.push "start inner")
          pure (events.modify (·.push "stop inner"))
        emitLabeled t "x"
        throw (IO.userError "boom")
    else
      withGroup 12 (pure ())
    emitLabeled t "b"
  checkEq "throw-rec: initial tree" (← t.render) "(root a b)"
  checkEq "throw-rec: initial effects" (← events.get) #["start outer"]
  boom.set true
  checkThrows "throw-rec: error propagates from drain" comp.drain
  checkEq "throw-rec: applier consistent after abort" (← t.render) "(root a b)"
  checkEq "throw-rec: failed pass launched nothing" (← events.get) #["start outer"]
  boom.set false
  comp.drain
  checkEq "throw-rec: recovers once the state changes" (← t.render) "(root a b)"
  checkEq "throw-rec: no double-started effects" (← events.get) #["start outer"]
  comp.dispose
  checkEq "throw-rec: dispose balanced" (← events.get) #["start outer", "stop outer"]

/-- A `DisposableEffect` key change inside a pass that later throws must
survive the abort: the retry re-runs `init` and fires the old `onForgotten`
and the new `onRemembered` exactly once each. -/
def keyChangeAbortRetry : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let key ← MutableState.create "a"
  let boom ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    let k ← key.get
    DisposableEffect k do
      events.modify (·.push s!"start {k}")
      pure (events.modify (·.push s!"stop {k}"))
    if ← boom.get then
      withGroup 11 (throw (IO.userError "boom"))
    else
      withGroup 12 (pure ())
  checkEq "keyAbort: initial" (← events.get) #["start a"]
  key.set "b"
  boom.set true
  checkThrows "keyAbort: failed pass propagates" comp.drain
  checkEq "keyAbort: failed pass dispatched nothing" (← events.get) #["start a"]
  boom.set false
  comp.drain
  checkEq "keyAbort: retry fires each end exactly once"
    (← events.get) #["start a", "stop a", "start b"]
  comp.dispose
  checkEq "keyAbort: dispose balanced" (← events.get)
    #["start a", "stop a", "start b", "stop b"]

/-- If the key reverts to its old value between the aborted pass and the
retry, the restored slot still matches and no spurious lifecycle fires. -/
def keyChangeAbortKeyReverts : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let key ← MutableState.create "a"
  let boom ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    let k ← key.get
    DisposableEffect k do
      events.modify (·.push s!"start {k}")
      pure (events.modify (·.push s!"stop {k}"))
    if ← boom.get then
      withGroup 11 (throw (IO.userError "boom"))
    else
      withGroup 12 (pure ())
  key.set "b"
  boom.set true
  checkThrows "keyRevert: failed pass propagates" comp.drain
  key.set "a"
  boom.set false
  comp.drain
  checkEq "keyRevert: no spurious lifecycle" (← events.get) #["start a"]
  comp.dispose
  checkEq "keyRevert: dispose stops the original" (← events.get) #["start a", "stop a"]

/-- A key change in a child scope that *completed* before a later sibling
threw: the abort must re-invalidate the completed child, or the retry skips
it (its slot already holds the new key) and the new effect never starts. -/
def keyChangeAbortInCompletedChild : IO Unit := do
  let t ← TestTree.create
  let events ← IO.mkRef (#[] : Array String)
  let tick ← MutableState.create (0 : Nat)
  let key ← MutableState.create "a"
  let boom ← MutableState.create false
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← tick.get
    restartable 2 do
      let k ← key.get
      DisposableEffect k do
        events.modify (·.push s!"start {k}")
        pure (events.modify (·.push s!"stop {k}"))
    restartable 3 do
      if ← boom.get then
        withGroup 11 (throw (IO.userError "boom"))
      else
        withGroup 12 (pure ())
  checkEq "keyNested: initial" (← events.get) #["start a"]
  tick.set 1
  key.set "b"
  boom.set true
  checkThrows "keyNested: failed pass propagates" comp.drain
  boom.set false
  comp.drain
  checkEq "keyNested: retry re-runs the completed child's replacement"
    (← events.get) #["start a", "stop a", "start b"]
  comp.dispose
  checkEq "keyNested: dispose balanced" (← events.get)
    #["start a", "stop a", "start b", "stop b"]

/-- An aborted pass leaves the open spine's node counts stale; they must be
refreshed so later standalone re-runs compute correct applier indices (the
silent Nat clamp in `propagateNodeDelta` previously ate the delta). -/
def staleSpineCountsAfterAbort : IO Unit := do
  let t ← TestTree.create
  let flagB ← MutableState.create false
  let flagC ← MutableState.create false
  let flagW ← MutableState.create false
  let boom ← MutableState.create false
  let content : Composable Unit := do
    withGroup 11 do
      restartable 2 do
        if ← flagB.get then
          withGroup 21 do
            emitLabeled t "b1"
            emitLabeled t "b2"
        else
          withGroup 22 (pure ())
      restartable 3 do
        if ← flagC.get then
          withGroup 31 (emitLabeled t "c1")
        else
          withGroup 32 (pure ())
      if ← boom.get then
        withGroup 41 (throw (IO.userError "boom"))
      else
        withGroup 42 (pure ())
    restartable 4 do
      if ← flagW.get then
        withGroup 51 (emitLabeled t "w")
      else
        withGroup 52 (pure ())
    emitLabeled t "z"
  let comp ← Composition.create t.applier content
  checkEq "stale: initial tree" (← t.render) "(root z)"
  flagB.set true
  flagC.set true
  boom.set true
  checkThrows "stale: recompose throw propagates" (comp.setContent content)
  checkEq "stale: completed children stay applied" (← t.render) "(root b1 b2 c1 z)"
  flagB.set false
  comp.drain
  checkEq "stale: standalone removal applied" (← t.render) "(root c1 z)"
  flagW.set true
  comp.drain
  checkEq "stale: later insert lands at the true index" (← t.render) "(root c1 w z)"

/-- All Runtime suites. -/
def run : IO Unit := do
  rememberSame
  rememberKeyedReinit
  conditional
  multiNodeConditional
  keyedReorder
  keyedMultiNodeMove
  scopeInsideNode
  scopeRerunAfterReorder
  stateTargeting
  latestRunReads
  alwaysNotify
  writeDuringRecomposition
  invalidationLoopDetected
  ancestorRerunsChild
  disposalOrdering
  disposableEffect
  sideEffect
  localDynamic
  localStatic
  localDefaultAndShadowing
  derivedState
  setContentAndDispose
  slotUnderflowReported
  derivedStateUnsubscribes
  derivedKeyChangeDisposes
  removalSeversSubtree
  throwOnInitialComposition
  throwDuringRecomposition
  keyChangeAbortRetry
  keyChangeAbortKeyReverts
  keyChangeAbortInCompletedChild
  staleSpineCountsAfterAbort

end Tests.Runtime
