import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# `composable` macro test group

Macro-authored compositions on the `TestApplier`: restart scoping, argument
skipping via `SkipEq`, automatic group keys for `if`/`match`/`for` (no
explicit `withGroup` in user code), `keyed` reorder inside macro loops,
`composable fun` content lambdas, and restart-closure argument capture.
-/

namespace Tests.MacroSuite
open Compose Tests.Harness

/-- Test-only wrapper whose `SkipEq` instance is always-equal, so plumbing
values (trees, counters, state cells) never disable skipping — the custom
end of the `SkipEq` extension point. -/
structure Stable (α : Type) where
  val : α

instance : SkipEq (Stable α) := ⟨fun _ _ => true⟩

/-- Leaf composable: bumps its run counter and emits the current count. -/
composable def counterText (t : Stable TestTree) (runs : Stable (IO.Ref Nat))
    (s : Stable (MutableState Nat)) : Composable Unit := do
  runs.val.modify (· + 1)
  emitText t.val s!"n{← s.val.get}"

/-- Parent that never reads the counter state itself. -/
composable def counterParent (t : Stable TestTree) (pruns cruns : Stable (IO.Ref Nat))
    (s : Stable (MutableState Nat)) : Composable Unit := do
  pruns.val.modify (· + 1)
  emitLabeled t.val "hdr"
  counterText t cruns s

/-- A state write re-runs only the macro-authored composable that read it;
the parent scope is not re-run. -/
def counterScope : IO Unit := do
  let t ← TestTree.create
  let pruns ← IO.mkRef (0 : Nat)
  let cruns ← IO.mkRef (0 : Nat)
  let s ← MutableState.create (0 : Nat)
  let comp ← Composition.create t.applier (counterParent ⟨t⟩ ⟨pruns⟩ ⟨cruns⟩ ⟨s⟩)
  checkEq "counter: initial tree" (← t.render) "(root hdr n0)"
  checkEq "counter: initial runs" ((← pruns.get), (← cruns.get)) (1, 1)
  s.set 3
  comp.drain
  checkEq "counter: only the reading scope re-ran" ((← pruns.get), (← cruns.get)) (1, 2)
  checkEq "counter: label reconciled in place" (← t.render) "(root hdr n3)"

/-- Skippable leaf: all data arguments are `BEq`. -/
composable def skipLeaf (runs : Stable (IO.Ref Nat)) (label : String) (n : Nat) :
    Composable Unit := do
  runs.val.modify (· + 1)

/-- Unskippable leaf: a function argument has no `BEq`, so the `SkipEq`
fallback reports it always-changed. -/
composable def unstableLeaf (runs : Stable (IO.Ref Nat)) (f : Nat → Nat) :
    Composable Unit := do
  runs.val.modify (· + 1)

/-- Parent recomposing on `tick`; children see equal or changed args. -/
composable def skipParent (pruns aruns bruns : Stable (IO.Ref Nat))
    (tick : Stable (MutableState Nat)) (label : Stable (MutableState String)) :
    Composable Unit := do
  let _ ← tick.val.get
  pruns.val.modify (· + 1)
  skipLeaf aruns (← label.val.get) 7
  unstableLeaf bruns (· + 1)

/-- Parent recomposition skips a child with `BEq`-equal args, re-runs it when
an arg changes, and never skips a child with a non-`BEq` (function) arg. -/
def skipping : IO Unit := do
  let t ← TestTree.create
  let pruns ← IO.mkRef (0 : Nat)
  let aruns ← IO.mkRef (0 : Nat)
  let bruns ← IO.mkRef (0 : Nat)
  let tick ← MutableState.create (0 : Nat)
  let label ← MutableState.create "a"
  let comp ← Composition.create t.applier
    (skipParent ⟨pruns⟩ ⟨aruns⟩ ⟨bruns⟩ ⟨tick⟩ ⟨label⟩)
  let runs : IO (Nat × Nat × Nat) :=
    return ((← pruns.get), (← aruns.get), (← bruns.get))
  checkEq "skip: initial runs" (← runs) (1, 1, 1)
  tick.set 1
  comp.drain
  checkEq "skip: equal args skipped, function arg did not" (← runs) (2, 1, 2)
  label.set "x"
  comp.drain
  checkEq "skip: changed arg re-ran the child" (← runs) (3, 2, 3)
  tick.set 2
  comp.drain
  checkEq "skip: skips again once args settle" (← runs) (4, 2, 4)

/-- `if` whose branches remember state and emit nodes — no explicit
`withGroup` anywhere. -/
composable def branchy (t : Stable TestTree) (inits : Stable (IO.Ref Nat))
    (seen : Stable (IO.Ref (Array String))) (flag : Stable (MutableState Bool)) :
    Composable Unit := do
  emitLabeled t.val "a"
  if ← flag.val.get then
    let n ← remember (inits.val.modifyGet fun k => (k, k + 1))
    seen.val.modify (·.push s!"T{n}")
    emitLabeled t.val "x"
  else
    let n ← remember (inits.val.modifyGet fun k => (k, k + 1))
    seen.val.modify (·.push s!"E{n}")
    emitLabeled t.val "y"
  emitLabeled t.val "b"

/-- Flipping an `if` inside a macro-authored composable inserts/removes nodes
at the right indices, and each branch owns its remembered state (values never
leak across branches; a re-appearing branch starts fresh). -/
def ifFlip : IO Unit := do
  let t ← TestTree.create
  let inits ← IO.mkRef (0 : Nat)
  let seen ← IO.mkRef (#[] : Array String)
  let flag ← MutableState.create true
  let comp ← Composition.create t.applier (branchy ⟨t⟩ ⟨inits⟩ ⟨seen⟩ ⟨flag⟩)
  checkEq "if: initial tree" (← t.render) "(root a x b)"
  checkEq "if: then-branch remembered" (← seen.get) #["T0"]
  flag.set false
  comp.drain
  checkEq "if: flipped tree" (← t.render) "(root a y b)"
  checkEq "if: else-branch got its own fresh slot" (← seen.get) #["T0", "E1"]
  flag.set true
  comp.drain
  checkEq "if: flipped back" (← t.render) "(root a x b)"
  checkEq "if: then-branch state was disposed, re-initialized" (← seen.get) #["T0", "E1", "T2"]
  checkEq "if: three initializations total" (← inits.get) 3

/-- Three-constructor scrutinee for the `match` test. -/
inductive Mode where
  | small
  | medium
  | large
  deriving BEq

/-- `match` over a three-constructor inductive, one branch multi-node, one
empty — again with no explicit `withGroup`. -/
composable def modal (t : Stable TestTree) (m : Stable (MutableState Mode)) :
    Composable Unit := do
  emitLabeled t.val "s"
  match ← m.val.get with
  | .small => emitLabeled t.val "sm"
  | .medium =>
    emitLabeled t.val "m1"
    emitLabeled t.val "m2"
  | .large => pure ()
  emitLabeled t.val "e"

/-- Cycling a `match` through all constructors keeps siblings at the right
indices for every alternative. -/
def matchModes : IO Unit := do
  let t ← TestTree.create
  let m ← MutableState.create Mode.small
  let comp ← Composition.create t.applier (modal ⟨t⟩ ⟨m⟩)
  checkEq "match: small" (← t.render) "(root s sm e)"
  m.set .medium
  comp.drain
  checkEq "match: medium emits two nodes" (← t.render) "(root s m1 m2 e)"
  m.set .large
  comp.drain
  checkEq "match: large emits none" (← t.render) "(root s e)"
  m.set .small
  comp.drain
  checkEq "match: back to small" (← t.render) "(root s sm e)"

/-- Positional `for`: each iteration gets a repeated positional group, so a
bare `remember` in the body is safe. -/
composable def loopy (t : Stable TestTree) (ctr : Stable (IO.Ref Nat))
    (items : Stable (MutableState (List String))) : Composable Unit := do
  for x in (← items.val.get) do
    let n ← remember (ctr.val.modifyGet fun k => (k, k + 1))
    emitText t.val s!"{x}{n}"

/-- `for` over a list: append reuses existing positions, removal at the end
disposes exactly the leftover iterations (their state is not resurrected). -/
def forLoop : IO Unit := do
  let t ← TestTree.create
  let ctr ← IO.mkRef (0 : Nat)
  let items ← MutableState.create ["a", "b"]
  let comp ← Composition.create t.applier (loopy ⟨t⟩ ⟨ctr⟩ ⟨items⟩)
  checkEq "for: initial tree" (← t.render) "(root a0 b1)"
  items.set ["a", "b", "c"]
  comp.drain
  checkEq "for: append kept earlier positions" (← t.render) "(root a0 b1 c2)"
  checkEq "for: no re-initialization on append" (← ctr.get) 3
  items.set ["a"]
  comp.drain
  checkEq "for: removal at end" (← t.render) "(root a0)"
  items.set ["a", "z"]
  comp.drain
  checkEq "for: re-grown position starts fresh" (← t.render) "(root a0 z3)"

/-- `for` whose body is a single `keyed` call: the data key is the iteration
group (the macro adds no extra positional wrapper). -/
composable def keyedLoop (t : Stable TestTree) (ctr : Stable (IO.Ref Nat))
    (items : Stable (MutableState (List String))) : Composable Unit := do
  for x in (← items.val.get) do
    keyed x do
      let n ← remember (ctr.val.modifyGet fun k => (k, k + 1))
      emitText t.val s!"{x}{n}"

/-- `keyed` per item inside a macro `for`: reorder preserves per-item
remembered state (nodes move instead of being recreated). -/
def keyedForLoop : IO Unit := do
  let t ← TestTree.create
  let ctr ← IO.mkRef (0 : Nat)
  let items ← MutableState.create ["a", "b", "c"]
  let comp ← Composition.create t.applier (keyedLoop ⟨t⟩ ⟨ctr⟩ ⟨items⟩)
  checkEq "keyedFor: initial tree" (← t.render) "(root a0 b1 c2)"
  let _ ← t.takeLog
  items.set ["c", "a", "b"]
  comp.drain
  checkEq "keyedFor: reorder preserved per-item state" (← t.render) "(root c2 a0 b1)"
  checkEq "keyedFor: exactly one applier move" (← t.takeLog) #["move 1 from 2 to 0 in root"]
  checkEq "keyedFor: nothing re-initialized" (← ctr.get) 3

/-- Helper invoking one content lambda from two distinct call-site groups. -/
def callTwice (mk : Nat → Composable Unit) : Composable Unit := do
  withGroup 101 (mk 0)
  withGroup 102 (mk 1)

/-- A `composable fun` content lambda invoked in two different call-site
groups keeps independent, stable remembered state in each. -/
def contentLambda : IO Unit := do
  let t ← TestTree.create
  let ctr ← IO.mkRef (0 : Nat)
  let s ← MutableState.create (0 : Nat)
  let comp ← Composition.create t.applier <| restartable 1 <| callTwice <|
    composable fun slot => do
      let v ← s.get
      let n ← remember (ctr.modifyGet fun k => (k, k + 1))
      emitText t s!"p{slot}v{v}n{n}"
  checkEq "fun: two independent positions" (← t.render) "(root p0v0n0 p1v0n1)"
  s.set 4
  comp.drain
  checkEq "fun: state independent and stable across recomposition"
    (← t.render) "(root p0v4n0 p1v4n1)"
  checkEq "fun: each position initialized exactly once" (← ctr.get) 2

/-- `if` inside `for` inside `if`, all auto-keyed by the macro. -/
composable def nestedFlow (t : Stable TestTree) (outer inner : Stable (MutableState Bool))
    (items : Stable (MutableState (List Nat))) : Composable Unit := do
  emitLabeled t.val "top"
  if ← outer.val.get then
    for i in (← items.val.get) do
      if ← inner.val.get then
        emitText t.val s!"a{i}"
      else
        emitText t.val s!"b{i}"
  else
    emitLabeled t.val "off"
  emitLabeled t.val "bot"

/-- Nested `if` inside `for` inside `if`: every flip and growth keeps sibling
indices correct. -/
def nestedControlFlow : IO Unit := do
  let t ← TestTree.create
  let outer ← MutableState.create true
  let inner ← MutableState.create true
  let items ← MutableState.create [1, 2]
  let comp ← Composition.create t.applier (nestedFlow ⟨t⟩ ⟨outer⟩ ⟨inner⟩ ⟨items⟩)
  checkEq "nest: initial" (← t.render) "(root top a1 a2 bot)"
  inner.set false
  comp.drain
  checkEq "nest: inner flip inside every iteration" (← t.render) "(root top b1 b2 bot)"
  items.set [1, 2, 3]
  comp.drain
  checkEq "nest: loop growth inside outer branch" (← t.render) "(root top b1 b2 b3 bot)"
  outer.set false
  comp.drain
  checkEq "nest: outer flip drops the loop" (← t.render) "(root top off bot)"
  outer.set true
  comp.drain
  checkEq "nest: outer flip restores the loop" (← t.render) "(root top b1 b2 b3 bot)"

/-- Child logging `label:state` on every run. -/
composable def stamp (log : Stable (IO.Ref (Array String)))
    (child : Stable (MutableState Nat)) (label : String) : Composable Unit := do
  log.val.modify (·.push s!"{label}:{← child.val.get}")

/-- Parent supplying `label` from its own state. -/
composable def stampParent (pruns : Stable (IO.Ref Nat)) (log : Stable (IO.Ref (Array String)))
    (labelSt : Stable (MutableState String)) (child : Stable (MutableState Nat)) :
    Composable Unit := do
  pruns.val.modify (· + 1)
  stamp log child (← labelSt.val.get)

/-- Restart closure: invalidating a scope directly (via state only it reads)
re-runs it with the argument values from its latest execution — including
values a parent recomposition supplied in between — without the parent. -/
def restartArgs : IO Unit := do
  let t ← TestTree.create
  let pruns ← IO.mkRef (0 : Nat)
  let log ← IO.mkRef (#[] : Array String)
  let labelSt ← MutableState.create "a"
  let child ← MutableState.create (0 : Nat)
  let comp ← Composition.create t.applier (stampParent ⟨pruns⟩ ⟨log⟩ ⟨labelSt⟩ ⟨child⟩)
  checkEq "restart: initial" (← log.get) #["a:0"]
  labelSt.set "b"
  comp.drain
  checkEq "restart: parent supplied a new argument" (← log.get) #["a:0", "b:0"]
  child.set 1
  comp.drain
  checkEq "restart: scope re-ran alone with its latest args" (← log.get) #["a:0", "b:0", "b:1"]
  checkEq "restart: parent ran only for the label change" (← pruns.get) 2

/-- All `composable`-macro suites. -/
def run : IO Unit := do
  counterScope
  skipping
  ifFlip
  matchModes
  forLoop
  keyedForLoop
  contentLambda
  nestedControlFlow
  restartArgs

end Tests.MacroSuite
