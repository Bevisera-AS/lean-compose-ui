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
  let s ← mutableStateOf (0 : Nat)
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
  let key ← mutableStateOf "a"
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
  let flag ← mutableStateOf false
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
  let flag ← mutableStateOf true
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
  let items ← mutableStateOf ["a", "b", "c"]
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
  let items ← mutableStateOf ["a", "b"]
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
  let flag ← mutableStateOf false
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
  let items ← mutableStateOf ["a", "b"]
  let flag ← mutableStateOf false
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
  let sA ← mutableStateOf (0 : Nat)
  let sB ← mutableStateOf (0 : Nat)
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
  let cond ← mutableStateOf true
  let sX ← mutableStateOf (0 : Nat)
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
  let s ← mutableStateOfAlwaysNotify (0 : Nat)
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
  let s ← mutableStateOf (0 : Nat)
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
  let s ← mutableStateOfAlwaysNotify (0 : Nat)
  checkThrows "loop: iteration cap reported" <|
    Composition.create t.applier <| restartable 1 do
      s.set ((← s.get) + 1)

/-- A parent scope re-running also re-runs its invalid children in place; the
queue then skips them (no double runs). Valid children are skipped entirely,
with node indices intact across the skip. -/
def ancestorRerunsChild : IO Unit := do
  let t ← TestTree.create
  let s ← mutableStateOf (0 : Nat)
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
  let flag ← mutableStateOf true
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
  let key ← mutableStateOf "a"
  let alive ← mutableStateOf true
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
  let s ← mutableStateOf (0 : Nat)
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
  let s ← mutableStateOf (1 : Nat)
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
  let s ← mutableStateOf (1 : Nat)
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
  let s ← mutableStateOf (0 : Nat)
  let computes ← IO.mkRef (0 : Nat)
  let d ← derivedStateOf do
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
  let s ← mutableStateOf false
  let comp ← Composition.create t.applier <| restartable 1 do
    let _ ← remember (pure (1 : Nat))
    if ← s.get then
      let _ ← remember (pure (2 : Nat))
  s.set true
  checkThrows "slots: underflow reported" comp.drain

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

end Tests.Runtime
