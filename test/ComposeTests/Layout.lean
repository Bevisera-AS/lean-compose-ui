import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Layout test group (`test/ComposeTests/Layout.lean`)

Measurement, placement, dirty tracking, and the draw walk of M4, driven
through real compositions on the `LayoutNode` applier. Measurement tests are
pure IO (no SDL window); the draw-walk test renders with the software
renderer under the dummy video driver and probes pixels, the same pattern as
the Draw group.
-/

namespace Tests.Layout
open Compose Tests.Harness

instance : ToString IntSize := ⟨fun s => s!"{s.width}x{s.height}"⟩
instance : ToString IntOffset := ⟨fun o => s!"({o.x},{o.y})"⟩

/-- Compose `content` into a fresh root `LayoutNode`. -/
private def composeTree (content : Composable Unit) : IO (LayoutNode × Composition) := do
  let root ← LayoutNode.create
  let comp ← Composition.create (LayoutNode.applier root) content
  return (root, comp)

/-- Node at a child-index path from the root. -/
private def nodeAt (root : LayoutNode) (path : List Nat) : IO LayoutNode :=
  path.foldlM (fun n i => n.child i) root

private def sizeAt (root : LayoutNode) (path : List Nat) : IO IntSize := do
  (← nodeAt root path).size

private def posAt (root : LayoutNode) (path : List Nat) : IO IntOffset := do
  (← nodeAt root path).position

/-- Wrap a policy with an invocation counter (measure-call probe). -/
private def probed (counter : IO.Ref Nat) (p : MeasurePolicy := .leaf) : MeasurePolicy :=
  fun ms m c => do counter.modify (· + 1); p ms m c

/-- A leaf `Layout` (children none, sized by its modifier). -/
private def leaf (m : Modifier) : Composable Unit := Layout m .leaf

/-- Child x-positions of the first child of `root`. -/
private def childXs (root : LayoutNode) (path : List Nat := [0]) : IO (List Int32) := do
  let n ← nodeAt root path
  let d ← n.data
  d.children.toList.mapM fun ch => return (← ch.data).position.x

/-- Child y-positions of the first child of `root`. -/
private def childYs (root : LayoutNode) (path : List Nat := [0]) : IO (List Int32) := do
  let n ← nodeAt root path
  let d ← n.data
  d.children.toList.mapM fun ch => return (← ch.data).position.y

/-! ## Modifier chain measurement -/

private def sizeAndPadding : IO Unit := do
  -- size within loose constraints
  do
    let (root, _) ← composeTree (leaf (Modifier.size 50 30))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "size: preferred size taken" (← sizeAt root [0]) (⟨50, 30⟩ : IntSize)
  -- size clamped by the incoming maximum
  do
    let (root, _) ← composeTree (leaf (Modifier.size 300 300))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "size: clamped to max constraints" (← sizeAt root [0]) (⟨200, 200⟩ : IntSize)
  -- padding adds to the content size; content offset shifts
  do
    let (root, _) ← composeTree (leaf (Modifier.padding (all := 10) |>.size 50 30))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "padding: outer = content + padding" (← sizeAt root [0]) (⟨70, 50⟩ : IntSize)
    checkEq "padding: content offset" (← (← nodeAt root [0]).contentOffset) (⟨10, 10⟩ : IntOffset)
  -- padding is clamped when it does not fit
  do
    let (root, _) ← composeTree (leaf (Modifier.padding (all := 10) |>.size 50 30))
    let _ ← root.remeasure { maxWidth := 60, maxHeight := 40 }
    checkEq "padding: clamped by max" (← sizeAt root [0]) (⟨60, 40⟩ : IntSize)
  -- nested padding through a parent/child tree
  do
    let (root, _) ← composeTree <|
      Layout (Modifier.padding (all := 10)) .root do
        leaf (Modifier.padding (all := 5) |>.size 20 20)
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "nested padding: child outer" (← sizeAt root [0, 0]) (⟨30, 30⟩ : IntSize)
    checkEq "nested padding: parent outer" (← sizeAt root [0]) (⟨50, 50⟩ : IntSize)
    checkEq "nested padding: child at content origin" (← posAt root [0, 0]) (⟨0, 0⟩ : IntOffset)

private def fillOffsetSizeIn : IO Unit := do
  -- fillMaxSize / fraction / fillMaxWidth
  do
    let (root, _) ← composeTree (leaf (Modifier.fillMaxSize))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 150 }
    checkEq "fillMaxSize: takes the bounded max" (← sizeAt root [0]) (⟨200, 150⟩ : IntSize)
  do
    let (root, _) ← composeTree (leaf (Modifier.fillMaxSize 0.5))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 150 }
    checkEq "fillMaxSize: fraction" (← sizeAt root [0]) (⟨100, 75⟩ : IntSize)
  do
    let (root, _) ← composeTree (leaf (Modifier.fillMaxWidth |>.height 40))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 150 }
    checkEq "fillMaxWidth + height" (← sizeAt root [0]) (⟨200, 40⟩ : IntSize)
  -- fill on an unbounded axis is a no-op (wraps to minimum)
  do
    let (root, _) ← composeTree (leaf (Modifier.fillMaxSize))
    let _ ← root.remeasure {}
    checkEq "fillMaxSize: unbounded wraps to min" (← sizeAt root [0]) (⟨0, 0⟩ : IntSize)
  -- padding + fillMaxSize: fill the padded space
  do
    let (root, _) ← composeTree <|
      Layout (Modifier.padding (all := 10)) .root do
        leaf (Modifier.fillMaxSize)
    let _ ← root.remeasure (.fixed 200 200)
    checkEq "padding+fill: parent fills incoming" (← sizeAt root [0]) (⟨200, 200⟩ : IntSize)
    checkEq "padding+fill: child fills padded space" (← sizeAt root [0, 0]) (⟨180, 180⟩ : IntSize)
  -- offset displaces content without changing the size
  do
    let (root, _) ← composeTree (leaf (Modifier.size 20 20 |>.offset 5 7))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "offset: size unchanged" (← sizeAt root [0]) (⟨20, 20⟩ : IntSize)
    checkEq "offset: content offset" (← (← nodeAt root [0]).contentOffset) (⟨5, 7⟩ : IntOffset)
  -- sizeIn: minimum applies; maximum clamps an inner size
  do
    let (root, _) ← composeTree (leaf (Modifier.sizeIn (minWidth := some 50) (minHeight := some 20)))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "sizeIn: minima apply" (← sizeAt root [0]) (⟨50, 20⟩ : IntSize)
  do
    let (root, _) ← composeTree (leaf (Modifier.sizeIn (maxWidth := some 30) |>.size 50 50))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "sizeIn: max clamps inner size" (← sizeAt root [0]) (⟨30, 50⟩ : IntSize)
  -- requiredSize overrides constraints; reported size is coerced, content centered
  do
    let (root, _) ← composeTree (leaf (Modifier.requiredSize 300 300))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "requiredSize: reported size coerced" (← sizeAt root [0]) (⟨200, 200⟩ : IntSize)
    checkEq "requiredSize: overflow centers content"
      (← (← nodeAt root [0]).contentOffset) (⟨-50, -50⟩ : IntOffset)
  -- wrapContentSize centers the content in the incoming bounds
  do
    let (root, _) ← composeTree (leaf (Modifier.wrapContentSize |>.size 20 20))
    let _ ← root.remeasure (.fixed 100 100)
    checkEq "wrapContentSize: fills the fixed bounds" (← sizeAt root [0]) (⟨100, 100⟩ : IntSize)
    checkEq "wrapContentSize: content centered"
      (← (← nodeAt root [0]).contentOffset) (⟨40, 40⟩ : IntOffset)

/-! ## Row / Column -/

private def rowArrangements : IO Unit := do
  let case' (arr : Arrangement) (expected : List Int32) (label : String) : IO Unit := do
    let (root, _) ← composeTree <| Row (horizontalArrangement := arr) do
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 10)
    let _ ← root.remeasure (.fixed 100 20)
    checkEq s!"row arrangement: {label} size" (← sizeAt root [0]) (⟨100, 20⟩ : IntSize)
    checkEq s!"row arrangement: {label}" (← childXs root) expected
  case' .start [0, 10, 20] "start"
  case' .«end» [70, 80, 90] "end"
  case' .center [35, 45, 55] "center"
  case' .spaceBetween [0, 45, 90] "spaceBetween"
  case' .spaceAround [12, 45, 78] "spaceAround"
  case' .spaceEvenly [18, 45, 73] "spaceEvenly"
  case' (.spacedBy 5) [0, 15, 30] "spacedBy 5"

private def rowCrossAlignment : IO Unit := do
  let case' (align : Alignment.Vertical) (expected : List Int32) (label : String) : IO Unit := do
    let (root, _) ← composeTree <| Row (verticalAlignment := align) do
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 20)
    let _ ← root.remeasure (.fixed 100 20)
    checkEq s!"row cross-align: {label}" (← childYs root) expected
  case' .top [0, 0] "top"
  case' .centerVertically [5, 0] "centerVertically"
  case' .bottom [10, 0] "bottom"

private def rowWeights : IO Unit := do
  -- 2:1 weights after a fixed sibling; exact division
  do
    let (root, _) ← composeTree <| Row do
      leaf (Modifier.weight 2 |>.height 10)
      leaf (Modifier.weight 1 |>.height 10)
      leaf (Modifier.size 10 10)
    let _ ← root.remeasure (.fixed 100 20)
    checkEq "weights 2:1: first share" (← sizeAt root [0, 0]) (⟨60, 10⟩ : IntSize)
    checkEq "weights 2:1: second share" (← sizeAt root [0, 1]) (⟨30, 10⟩ : IntSize)
    checkEq "weights 2:1: fixed sibling" (← sizeAt root [0, 2]) (⟨10, 10⟩ : IntSize)
    checkEq "weights 2:1: positions" (← childXs root) [0, 60, 90]
  -- remainder pixels distributed round-robin so totals are exact
  do
    let (root, _) ← composeTree <| Row do
      leaf (Modifier.weight 1 |>.height 10)
      leaf (Modifier.weight 1 |>.height 10)
      leaf (Modifier.weight 1 |>.height 10)
    let _ ← root.remeasure (.fixed 100 20)
    checkEq "weights remainder: 100/3 = 34+33+33"
      [(← sizeAt root [0, 0]).width, (← sizeAt root [0, 1]).width, (← sizeAt root [0, 2]).width]
      [34, 33, 33]
    checkEq "weights remainder: positions" (← childXs root) [0, 34, 67]
  -- fill := false leaves the share as an upper bound only
  do
    let (root, _) ← composeTree <| Row do
      leaf (Modifier.weight 1 (fill := false) |>.width 10 |>.height 10)
      leaf (Modifier.size 20 10)
    let _ ← root.remeasure (.fixed 100 20)
    checkEq "weight no-fill: child keeps its own width" (← sizeAt root [0, 0]) (⟨10, 10⟩ : IntSize)
    checkEq "weight no-fill: row still fills min" (← sizeAt root [0]) (⟨100, 20⟩ : IntSize)
    checkEq "weight no-fill: positions" (← childXs root) [0, 10]

private def columnBasics : IO Unit := do
  do
    let (root, _) ← composeTree <| Column (verticalArrangement := .spaceEvenly) do
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 10)
    let _ ← root.remeasure (.fixed 20 100)
    checkEq "column spaceEvenly: y positions" (← childYs root) [18, 45, 73]
    checkEq "column spaceEvenly: x stays start" (← childXs root) [0, 0, 0]
  do
    let (root, _) ← composeTree <| Column (verticalArrangement := .spacedBy 4)
        (horizontalAlignment := .«end») do
      leaf (Modifier.size 10 10)
      leaf (Modifier.size 10 10)
    let _ ← root.remeasure (.fixed 20 100)
    checkEq "column spacedBy: y positions" (← childYs root) [0, 14]
    checkEq "column align end: x positions" (← childXs root) [10, 10]
  -- Column weight
  do
    let (root, _) ← composeTree <| Column do
      leaf (Modifier.size 10 10)
      leaf (Modifier.weight 1 |>.width 10)
    let _ ← root.remeasure (.fixed 20 100)
    checkEq "column weight: fills the rest" (← sizeAt root [0, 1]) (⟨10, 90⟩ : IntSize)
    checkEq "column weight: position" (← childYs root) [0, 10]

private def boxAndSpacer : IO Unit := do
  do
    let (root, _) ← composeTree <| Box (contentAlignment := .center) do
      leaf (Modifier.size 20 20)
      leaf (Modifier.align .bottomEnd (m := Modifier.size 20 20))
      leaf (Modifier.matchParentSize)
    let _ ← root.remeasure (.fixed 100 100)
    checkEq "box: content-aligned child centers" (← posAt root [0, 0]) (⟨40, 40⟩ : IntOffset)
    checkEq "box: per-child align overrides" (← posAt root [0, 1]) (⟨80, 80⟩ : IntOffset)
    checkEq "box: matchParentSize child" (← sizeAt root [0, 2]) (⟨100, 100⟩ : IntSize)
    checkEq "box: matchParentSize at origin" (← posAt root [0, 2]) (⟨0, 0⟩ : IntOffset)
  -- Box wraps its largest child under loose constraints
  do
    let (root, _) ← composeTree <| Box do
      leaf (Modifier.size 20 30)
      leaf (Modifier.size 30 10)
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "box: wraps the largest child" (← sizeAt root [0]) (⟨30, 30⟩ : IntSize)
  -- Spacer
  do
    let (root, _) ← composeTree (Spacer (Modifier.size 16 8))
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "spacer: sized by modifier" (← sizeAt root [0]) (⟨16, 8⟩ : IntSize)
  do
    let (root, _) ← composeTree (Spacer)
    let _ ← root.remeasure { maxWidth := 200, maxHeight := 200 }
    checkEq "spacer: bare wraps to zero" (← sizeAt root [0]) (⟨0, 0⟩ : IntSize)

/-! ## Intrinsic width (two-pass measurement) -/

private def intrinsicWidthBasics : IO Unit := do
  -- size to the widest child; fill-width children stretch to the winner
  do
    let (root, _) ← composeTree <| Column (modifier := Modifier.widthIntrinsicMax) do
      leaf (Modifier.fillMaxWidth |>.height 10)
      leaf (Modifier.size 80 10)
      leaf (Modifier.size 50 10)
    let _ ← root.remeasure { maxWidth := 400, maxHeight := 400 }
    checkEq "intrinsic: column sizes to widest child" (← sizeAt root [0]) (⟨80, 30⟩ : IntSize)
    checkEq "intrinsic: fill child stretches to the winner"
      (← sizeAt root [0, 0]) (⟨80, 10⟩ : IntSize)
    checkEq "intrinsic: children at x 0" (← childXs root) [0, 0, 0]
    checkEq "intrinsic: children stacked" (← childYs root) [0, 10, 20]
  -- the natural width clamps into a bounded incoming maximum
  do
    let (root, _) ← composeTree <| Column (modifier := Modifier.widthIntrinsicMax) do
      leaf (Modifier.size 80 10)
      leaf (Modifier.fillMaxWidth |>.height 10)
    let _ ← root.remeasure { maxWidth := 60, maxHeight := 400 }
    checkEq "intrinsic: natural width clamps to max" (← sizeAt root [0]) (⟨60, 20⟩ : IntSize)
    checkEq "intrinsic: fill child gets the clamped width"
      (← sizeAt root [0, 1]) (⟨60, 10⟩ : IntSize)
  -- an inner minimum (sizeIn) floors the probe result
  do
    let (root, _) ← composeTree <|
      Column (modifier := Modifier.widthIntrinsicMax |>.sizeIn (minWidth := some 112)) do
        leaf (Modifier.size 50 10)
        leaf (Modifier.fillMaxWidth |>.height 10)
    let _ ← root.remeasure { maxWidth := 400, maxHeight := 400 }
    checkEq "intrinsic: inner minWidth floors the result"
      (← sizeAt root [0]) (⟨112, 20⟩ : IntSize)
    checkEq "intrinsic: fill child fills the floored width"
      (← sizeAt root [0, 1]) (⟨112, 10⟩ : IntSize)

/-- The soundness proof of two-pass measurement: a child whose reported size
depends on its constraints ("greedy": takes the bounded max width, wraps to 30
when unbounded) is measured exactly twice under the intrinsic wrapper — first
width-unbounded (probe), then at the fixed winner width — and the node's
cached size and placement come from the SECOND measure (`measureIn`
recomputes because the constraints changed; the `.custom` chain fold keeps
the last inner measurement). -/
private def intrinsicTwoPassSound : IO Unit := do
  let log ← IO.mkRef (#[] : Array Constraints)
  let greedy : MeasurePolicy := fun _ _ c => do
    log.modify (·.push c)
    return { size := ⟨if c.hasBoundedWidth then c.maxWidth else 30, 10⟩ }
  let (root, _) ← composeTree <| Column (modifier := Modifier.widthIntrinsicMax) do
    Layout {} greedy
    leaf (Modifier.size 80 10)
  let c : Constraints := { maxWidth := 400, maxHeight := 400 }
  let _ ← root.remeasure c
  let cs ← log.get
  checkEq "two-pass: greedy child measured exactly twice" cs.size 2
  check "two-pass: probe is width-unbounded"
    (cs[0]!.maxWidth == Constraints.infinity)
  checkEq "two-pass: real pass sees the winner width" cs[1]!.maxWidth 80
  checkEq "two-pass: second measure wins (cached size)"
    (← sizeAt root [0, 0]) (⟨80, 10⟩ : IntSize)
  checkEq "two-pass: wrapper sized by the second pass" (← sizeAt root [0]) (⟨80, 20⟩ : IntSize)
  checkEq "two-pass: placement from the second pass" (← childYs root) [0, 10]
  -- Unchanged constraints still short-circuit: a clean re-pass measures nothing.
  let _ ← root.remeasure c
  checkEq "two-pass: clean re-pass measures nothing" (← log.get).size 2

/-! ## Invalidation and caching -/

private def recompositionRemeasures : IO Unit := do
  let s ← MutableState.create (30 : Dp)
  let cnt ← IO.mkRef (0 : Nat)
  let (root, comp) ← composeTree <| restartable 1 do
    let v ← s.get
    Layout (Modifier.size v v) (probed cnt)
  let c : Constraints := { maxWidth := 200, maxHeight := 200 }
  let _ ← root.remeasure c
  checkEq "recompose: initial size" (← sizeAt root [0]) (⟨30, 30⟩ : IntSize)
  checkEq "recompose: initial measure count" (← cnt.get) 1
  s.set 50
  comp.drain
  let _ ← root.remeasure c
  checkEq "recompose: state-driven size change" (← sizeAt root [0]) (⟨50, 50⟩ : IntSize)
  checkEq "recompose: exactly one extra measure" (← cnt.get) 2

private def constraintsShortCircuit : IO Unit := do
  let cnt ← IO.mkRef (0 : Nat)
  let (root, _) ← composeTree <| Layout (Modifier.size 40 40) (probed cnt)
  let c : Constraints := { maxWidth := 200, maxHeight := 200 }
  let _ ← root.remeasure c
  checkEq "short-circuit: first pass measures" (← cnt.get) 1
  let _ ← root.remeasure c
  checkEq "short-circuit: unchanged constraints skip" (← cnt.get) 1
  let _ ← root.remeasure { maxWidth := 100, maxHeight := 100 }
  checkEq "short-circuit: new constraints re-measure" (← cnt.get) 2

private def measureStateTargeting : IO Unit := do
  let s ← MutableState.create (20 : Nat)
  let cntA ← IO.mkRef (0 : Nat)
  let cntB ← IO.mkRef (0 : Nat)
  let cntP ← IO.mkRef (0 : Nat)
  -- A's policy reads `s` during measure and sizes from it.
  let policyA : MeasurePolicy := fun _ _ _ => do
    cntA.modify (· + 1)
    let v ← s.get
    return { size := ⟨Int32.ofNat v, 10⟩ }
  let (root, _) ← composeTree <| Layout {} (probed cntP .root) do
    Layout {} policyA
    Layout (Modifier.size 10 10) (probed cntB)
  let c : Constraints := Constraints.fixed 100 100
  let _ ← root.remeasure c
  checkEq "measure-state: initial counts" ((← cntA.get), (← cntB.get), (← cntP.get)) (1, 1, 1)
  checkEq "measure-state: initial size" (← sizeAt root [0, 0]) (⟨20, 10⟩ : IntSize)
  -- equal write is a no-op
  s.set 20
  let _ ← root.remeasure c
  checkEq "measure-state: equal write no-op" ((← cntA.get), (← cntB.get), (← cntP.get)) (1, 1, 1)
  -- a real write invalidates exactly node A; the clean sibling stays cached;
  -- A's size changed, so the parent's policy re-runs (its size depends on A)
  s.set 30
  let _ ← root.remeasure c
  checkEq "measure-state: dirty node re-measured once more"
    ((← cntA.get), (← cntB.get)) (2, 1)
  checkEq "measure-state: parent re-ran (child size changed)" (← cntP.get) 2
  checkEq "measure-state: new size" (← sizeAt root [0, 0]) (⟨30, 10⟩ : IntSize)

private def survivingSizeStopsPropagation : IO Unit := do
  let s ← MutableState.create (0 : Nat)
  let cntA ← IO.mkRef (0 : Nat)
  let cntP ← IO.mkRef (0 : Nat)
  -- A reads `s` in measure but its size does not depend on it.
  let policyA : MeasurePolicy := fun _ _ _ => do
    cntA.modify (· + 1)
    let _ ← s.get
    return { size := ⟨15, 15⟩ }
  let (root, _) ← composeTree <| Layout {} (probed cntP .root) do
    Layout {} policyA
  let c : Constraints := Constraints.fixed 100 100
  let _ ← root.remeasure c
  checkEq "surviving-size: initial counts" ((← cntA.get), (← cntP.get)) (1, 1)
  s.set 1
  let _ ← root.remeasure c
  checkEq "surviving-size: only the reading node re-measures"
    ((← cntA.get), (← cntP.get)) (2, 1)

/-- A state write during a LATER sibling's measure that invalidates an
EARLIER (already-visited) sibling must survive the relayout pass: the mark
keeps a dirty path connected to the root and the owner hook fires, so the
follow-up pass re-measures the earlier sibling instead of leaving it stale
forever. -/
private def midPassDirtyOfVisitedSibling : IO Unit := do
  let s ← MutableState.create (10 : Nat)      -- A's width source
  let trigger ← MutableState.create (0 : Nat) -- B's remeasure trigger
  let cntA ← IO.mkRef (0 : Nat)
  let policyA : MeasurePolicy := fun _ _ _ => do
    cntA.modify (· + 1)
    return { size := ⟨Int32.ofNat (← s.get), 10⟩ }
  -- B (measured after A) dirties A mid-pass once armed.
  let policyB : MeasurePolicy := fun _ _ _ => do
    if (← trigger.get) == 1 then s.set 30
    return { size := ⟨10, 10⟩ }
  let (root, _) ← composeTree <| Layout {} .root do
    Layout {} policyA
    Layout {} policyB
  let hookFires ← IO.mkRef (0 : Nat)
  root.setOnRequestRemeasure (hookFires.modify (· + 1))
  let c : Constraints := Constraints.fixed 100 100
  let _ ← root.remeasure c
  checkEq "mid-pass dirty: initial A size" (← sizeAt root [0, 0]) (⟨10, 10⟩ : IntSize)
  trigger.set 1
  let fires0 ← hookFires.get
  let _ ← root.remeasure c
  check "mid-pass dirty: owner hook fired for the in-pass mark"
    ((← hookFires.get) > fires0)
  -- The follow-up pass (the frame the hook scheduled) reaches A.
  let _ ← root.remeasure c
  checkEq "mid-pass dirty: follow-up pass re-measures A"
    (← sizeAt root [0, 0]) (⟨30, 10⟩ : IntSize)
  -- and the tree settles: a clean re-pass measures nothing further.
  let a ← cntA.get
  let _ ← root.remeasure c
  checkEq "mid-pass dirty: settled after the follow-up" (← cntA.get) a

/-- The shared-`ScrollState` sticky-header pattern (`Foundation/Lazy.lean`):
a header strip sharing the main container's scroll state, composed BEFORE
it. Scrolled near the end, then the main content shrinks: the main measure
re-clamps `valueState` (`Foundation/Scroll.lean`), invalidating the header's
already-visited scroll node mid-pass — the header must still end up at the
re-clamped offset. -/
private def sharedScrollStickyHeader : IO Unit := do
  let s ← Compose.ScrollState.create
  let wide ← MutableState.create true -- main content: 1000px wide, then 300px
  Compose.Test.runComposeTest (theme := none)
      (Column (Tests.restartable 1 do
        let w : Dp := if ← wide.get then 1000 else 300
        Box (modifier := Modifier.width 200 |>.height 20 |>.horizontalScroll s) do
          Box (modifier := Modifier.testTag "header" |>.width 1000 |>.height 20)
        Box (modifier := Modifier.width 200 |>.height 100 |>.horizontalScroll s) do
          Box (modifier := Modifier.testTag "main" |>.width w |>.height 100))) do
      s.scrollTo 10000 -- clamps to maxValue = 1000 - 200 = 800
      Compose.Test.awaitIdle
      Compose.Test.assertThat (.tag "header") "scrolled to the end (x = -800)"
        (·.bounds.left == -800)
      Compose.Test.assertThat (.tag "main") "content at the end (x = -800)"
        (·.bounds.left == -800)
      wide.set false -- maxValue drops to 100; main's measure re-clamps value
      Compose.Test.awaitIdle
      Compose.Test.assertThat (.tag "main") "re-clamped content (x = -100)"
        (·.bounds.left == -100)
      Compose.Test.assertThat (.tag "header") "header follows the re-clamp (x = -100)"
        (·.bounds.left == -100)
      checkEq "sticky header: scroll value re-clamped" (← s.value).toString "100.000000"

/-! ## Draw walk (pixel probes) -/

private def drawWalk : IO Unit := do
  let win ← Sdl.createWindow "compose-layout" 200 300
  let ren ← Sdl.createRenderer win (some Sdl.softwareRenderer)
  ren.setDrawColor 0 0 0 255
  ren.clear
  let (root, _) ← composeTree <| Column (modifier := Modifier.fillMaxSize) do
    -- y ∈ [0, 50): plain red background
    leaf (Modifier.size 50 50 |>.background .red)
    -- y ∈ [50, 100): left padding shifts the green fill to x ∈ [10, 60)
    leaf (Modifier.padding (left := some 10) |>.size 50 50 |>.background .green)
    -- y ∈ [100, 140): blue fill with a 4px white border just inside
    leaf (Modifier.size 40 40 |>.background .blue |>.border 4 .white)
    -- y ∈ [140, 160): stacking order — yellow drawn over red
    Box do
      leaf (Modifier.size 20 20 |>.background .red)
      leaf (Modifier.size 20 20 |>.background .yellow)
    -- y ∈ [160, 200): circle clip scopes the cyan fill
    leaf (Modifier.size 40 40 |>.clip .circle |>.background .cyan)
    -- y ∈ [200, 240): alpha scopes the white fill
    leaf (Modifier.size 40 40 |>.alpha 0.5 |>.background .white)
  let _ ← root.remeasure (.fixed 200 300)
  Compose.Draw.DrawScope.run ren {} (root.drawTree)
  let shot ← ren.readPixels
  check "draw: first box red" (colorNear (← shot.readPixel 5 5) 255 0 0)
  check "draw: untouched background stays black" (colorNear (← shot.readPixel 120 5) 0 0 0)
  check "draw: padding region not painted" (colorNear (← shot.readPixel 5 75) 0 0 0)
  check "draw: padded green at shifted position" (colorNear (← shot.readPixel 15 75) 0 255 0)
  check "draw: bordered box center blue" (colorNear (← shot.readPixel 20 120) 0 0 255)
  check "draw: border over background (left edge)" (colorNear (← shot.readPixel 2 120) 255 255 255)
  check "draw: border over background (top edge)" (colorNear (← shot.readPixel 20 102) 255 255 255)
  check "draw: later sibling stacks on top" (colorNear (← shot.readPixel 5 145) 255 255 0)
  check "draw: clip circle center painted" (colorNear (← shot.readPixel 20 180) 0 255 255)
  check "draw: clip circle corner clipped" (colorNear (← shot.readPixel 2 162) 0 0 0)
  check "draw: alpha halves the fill" (colorNear (← shot.readPixel 20 220) 128 128 128)

/-- The Layout group. -/
def run : IO Unit := do
  Sdl.init .video
  sizeAndPadding
  fillOffsetSizeIn
  rowArrangements
  rowCrossAlignment
  rowWeights
  columnBasics
  boxAndSpacer
  intrinsicWidthBasics
  intrinsicTwoPassSound
  recompositionRemeasures
  constraintsShortCircuit
  measureStateTargeting
  survivingSizeStopsPropagation
  midPassDirtyOfVisitedSibling
  scenario "shared-scroll sticky header re-clamp" sharedScrollStickyHeader
  drawWalk

end Tests.Layout
