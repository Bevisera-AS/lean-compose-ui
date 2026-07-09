import Compose.Ui.Layout

namespace Compose

/-!
# Standard layouts (`Compose/Foundation/Layouts.lean`)

`Row`, `Column`, `Box`, and `Spacer` over the `Layout` primitive, mirroring
`androidx.compose.foundation.layout`. Main-axis arrangement math and weight
distribution are pure helpers (`Arrangement.positions`,
`distributeWeights`), `#guard`-tested against Compose's numeric behavior
(float accumulation with per-position rounding; round-robin remainder pixels
for weights so totals are exact).
-/

/-- Main-axis arrangement of a `Row`/`Column`'s children. `top`/`bottom` are
the `Column` spellings of `start`/`end`. Mirrors
`androidx.compose.foundation.layout.Arrangement`. -/
inductive Arrangement where
  | start
  | «end»
  | top
  | bottom
  | center
  | spaceBetween
  | spaceAround
  | spaceEvenly
  /-- Fixed spacing between consecutive children, packed at the start.
  Mirrors `Arrangement.spacedBy`. -/
  | spacedBy (space : Dp)
  deriving Repr, BEq, Inhabited

/-- Accumulate positions in `Float32` (Compose's arrangement math), rounding
each emitted position. -/
private def accumulatePositions (sizes : Array Int32) (start gap : Float32) :
    Array Int32 :=
  (sizes.foldl (init := ((#[] : Array Int32), start)) fun (out, cur) sz =>
    (out.push (roundHalfUp cur), cur + sz.toFloat32 + gap)).1

namespace Arrangement

/-- Main-axis positions for children of the given `sizes` inside `total` px.
`spacingPx` is the resolved `spacedBy` spacing (ignored by the other
arrangements). Mirrors `Arrangement.Horizontal/Vertical.arrange`. -/
def positions (a : Arrangement) (total : Int32) (sizes : Array Int32)
    (spacingPx : Int32 := 0) : Array Int32 :=
  if sizes.isEmpty then #[] else
  let n := sizes.size
  let free := (total - sizes.foldl (· + ·) 0).toFloat32
  match a with
  | .start | .top => accumulatePositions sizes 0 0
  | .«end» | .bottom => accumulatePositions sizes free 0
  | .center => accumulatePositions sizes (free / 2) 0
  | .spacedBy _ => accumulatePositions sizes 0 spacingPx.toFloat32
  | .spaceBetween =>
    accumulatePositions sizes 0 (if n > 1 then free / (n - 1).toFloat32 else 0)
  | .spaceAround =>
    let gap := free / n.toFloat32
    accumulatePositions sizes (gap / 2) gap
  | .spaceEvenly =>
    let gap := free / (n + 1).toFloat32
    accumulatePositions sizes gap gap

#guard positions .start 100 #[10, 10, 10] == #[0, 10, 20]
#guard positions .«end» 100 #[10, 10, 10] == #[70, 80, 90]
#guard positions .center 100 #[10, 10, 10] == #[35, 45, 55]
#guard positions .spaceBetween 100 #[10, 10, 10] == #[0, 45, 90]
#guard positions .spaceAround 100 #[10, 10, 10] == #[12, 45, 78]
#guard positions .spaceEvenly 100 #[10, 10, 10] == #[18, 45, 73]
#guard positions (.spacedBy 5) 100 #[10, 10, 10] (spacingPx := 5) == #[0, 15, 30]
#guard positions .top 100 #[10, 20] == #[0, 10]
#guard positions .bottom 100 #[10, 20] == #[70, 80]
#guard positions .center 100 #[10] == #[45]
#guard positions .spaceBetween 100 #[10] == #[0]     -- single child packs at start
#guard positions .spaceAround 100 #[10] == #[45]
#guard positions .start 100 (#[] : Array Int32) == #[]
#guard positions .center 30 #[10, 10, 10] == #[0, 10, 20] -- no free space

end Arrangement

/-- Split `available` px among weighted children, Compose-exact: each child
gets `available / totalWeight × weight` rounded, then the leftover remainder
pixels are distributed one per child (round-robin, in order, clamped at 0) so
the shares always sum to `available`. Mirrors the weighted pass of
`RowColumnMeasurePolicy`. -/
def distributeWeights (available : Int32) (weights : Array Float32) : Array Int32 :=
  let total := weights.foldl (· + ·) 0
  if total <= 0 then weights.map fun _ => 0 else Id.run do
    let unit := available.toFloat32 / total
    let mut out := weights.map fun w => max 0 (roundHalfUp (unit * w))
    let mut rem := available - out.foldl (· + ·) 0
    let mut i := 0
    while rem != 0 && i < out.size do
      let s : Int32 := if rem > 0 then 1 else -1
      out := out.set! i (max 0 (out[i]! + s))
      rem := rem - s
      i := i + 1
    return out

#guard distributeWeights 90 #[2, 1] == #[60, 30]
#guard distributeWeights 100 #[2, 1] == #[67, 33]
#guard distributeWeights 10 #[1, 1, 1] == #[4, 3, 3]   -- +1 remainder to the first
#guard distributeWeights 11 #[1, 1, 1] == #[3, 4, 4]   -- -1 remainder from the first
#guard (distributeWeights 11 #[1, 1, 1]).foldl (· + ·) 0 == 11
#guard distributeWeights 0 #[1, 2] == #[0, 0]
#guard distributeWeights 100 (#[] : Array Float32) == #[]
#guard distributeWeights 100 #[0, 0] == #[0, 0]

/-- Stable identity for a policy's inputs (for `Layout`'s `policyInputs`). -/
private def arrangementKey : Arrangement → UInt64
  | .start => 1
  | .«end» => 2
  | .top => 3
  | .bottom => 4
  | .center => 5
  | .spaceBetween => 6
  | .spaceAround => 7
  | .spaceEvenly => 8
  | .spacedBy s => mixKeys 9 s.value.toBits.toUInt64

/-- The shared `Row`/`Column` measure policy: unweighted children measure
first against the space that remains; weighted children then split the
leftover via `distributeWeights` (`fill` fixes their main-axis size, else it
is only an upper bound); the container wraps its content clamped into the
incoming constraints; placement combines `Arrangement.positions` on the main
axis with the cross-axis alignment bias. Mirrors `RowColumnMeasurePolicy`. -/
private def rowColumnPolicy (isRow : Bool) (arr : Arrangement) (crossBias : Float32) :
    MeasurePolicy := fun scope children c => do
  let spacing : Int32 := match arr with
    | .spacedBy s => scope.roundToPx s
    | _ => 0
  let mainMax := if isRow then c.maxWidth else c.maxHeight
  let mainMin := if isRow then c.minWidth else c.minHeight
  let crossMax := if isRow then c.maxHeight else c.maxWidth
  let crossMin := if isRow then c.minHeight else c.minWidth
  let bounded := mainMax != Constraints.infinity
  let nKids := children.size
  let totalSpacing : Int32 := if nKids > 1 then spacing * Int32.ofNat (nKids - 1) else 0
  let childC (mn mx : Int32) : Constraints :=
    if isRow then { minWidth := mn, maxWidth := mx, maxHeight := crossMax }
    else { minHeight := mn, maxHeight := mx, maxWidth := crossMax }
  -- Pass 1: unweighted children, against the remaining main-axis space.
  let mut placed : Array (Option Placeable) := .replicate nKids none
  let mut fixedUsed : Int32 := 0
  let mut totalWeight : Float32 := 0
  for i in [0:nKids] do
    let m := children[i]!
    if m.parentData.weight > 0 then
      totalWeight := totalWeight + m.parentData.weight
    else
      let avail := if bounded then max 0 (mainMax - totalSpacing - fixedUsed)
                   else Constraints.infinity
      let p ← m.measure (childC 0 avail)
      fixedUsed := fixedUsed + (if isRow then p.width else p.height)
      placed := placed.set! i (some p)
  -- Pass 2: weighted children split the remaining space.
  if totalWeight > 0 then
    let target := if bounded then mainMax else mainMin
    let shares := distributeWeights (max 0 (target - totalSpacing - fixedUsed))
      (children.filterMap fun m =>
        if m.parentData.weight > 0 then some m.parentData.weight else none)
    let mut wi := 0
    for i in [0:nKids] do
      let m := children[i]!
      if m.parentData.weight > 0 then
        let share := shares[wi]!
        wi := wi + 1
        placed := placed.set! i (some (← m.measure
          (childC (if m.parentData.fill then share else 0) share)))
  -- Container size wraps content, clamped into the incoming constraints.
  let mains := placed.map fun p? => match p? with
    | some p => if isRow then p.width else p.height
    | none => 0
  let crossUsed := placed.foldl (init := (0 : Int32)) fun acc p? => match p? with
    | some p => max acc (if isRow then p.height else p.width)
    | none => acc
  let mainSize := min (max (mains.foldl (· + ·) 0 + totalSpacing) mainMin) mainMax
  let crossSize := min (max crossUsed crossMin) crossMax
  let poss := arr.positions mainSize mains spacing
  return {
    size := if isRow then ⟨mainSize, crossSize⟩ else ⟨crossSize, mainSize⟩
    placement := do
      for i in [0:nKids] do
        if let some p := placed[i]! then
          let cross := Alignment.alignBias crossBias
            (if isRow then p.height else p.width) crossSize
          p.placeAt (if isRow then ⟨poss[i]!, cross⟩ else ⟨cross, poss[i]!⟩) }

namespace Modifier

/-- Size this child proportionally to `w` within the free main-axis space of
its `Row`/`Column` (measured after unweighted siblings). With `fill` the
child is forced to exactly its share; otherwise the share is only an upper
bound. Only meaningful on a direct child of `Row`/`Column` (ignored
elsewhere). Mirrors `RowScope.weight`/`ColumnScope.weight` (a plain modifier
here — no receiver scopes). -/
def weight (w : Float32) (fill : Bool := true) (m : Modifier := {}) : Modifier :=
  m.withParentData { weight := w, fill }

end Modifier

/-- Lay children out horizontally. Mirrors
`androidx.compose.foundation.layout.Row`. -/
def Row (content : Composable Unit := pure ())
    (modifier : Modifier := {})
    (horizontalArrangement : Arrangement := .start)
    (verticalAlignment : Alignment.Vertical := .top) : Composable Unit :=
  Layout modifier (rowColumnPolicy true horizontalArrangement verticalAlignment.bias)
    content
    (policyInputs := some (mixKeys 0x526f77 (mixKeys (arrangementKey horizontalArrangement)
      verticalAlignment.bias.toBits.toUInt64)))

/-- Lay children out vertically. Mirrors
`androidx.compose.foundation.layout.Column`. -/
def Column (content : Composable Unit := pure ())
    (modifier : Modifier := {})
    (verticalArrangement : Arrangement := .top)
    (horizontalAlignment : Alignment.Horizontal := .start) : Composable Unit :=
  Layout modifier (rowColumnPolicy false verticalArrangement horizontalAlignment.bias)
    content
    (policyInputs := some (mixKeys 0x436f6c (mixKeys (arrangementKey verticalArrangement)
      horizontalAlignment.bias.toBits.toUInt64)))

namespace Modifier

/-- Override the enclosing box's `contentAlignment` for this child. Only
meaningful on a direct child of `Box` (ignored elsewhere). Mirrors
`BoxScope.align` (a plain modifier here — no receiver scopes). -/
def align (a : Alignment) (m : Modifier := {}) : Modifier :=
  m.withParentData { align := some (a.horizontalBias, a.verticalBias) }

/-- Size this child to the enclosing box's final size (it does not influence
that size). Only meaningful on a direct child of `Box` (ignored elsewhere).
Mirrors `BoxScope.matchParentSize`. -/
def matchParentSize (m : Modifier := {}) : Modifier :=
  m.withParentData { matchParentSize := true }

end Modifier

/-- `Box` measure: regular children measure loose and the box wraps the
largest (clamped); `matchParentSize` children then measure at exactly the
box's size; placement aligns each child by its `align` override or the box's
`contentAlignment`. Mirrors `BoxMeasurePolicy`. -/
private def boxPolicy (contentAlign : Alignment) : MeasurePolicy := fun _ children c => do
  if children.isEmpty then
    return { size := ⟨c.minWidth, c.minHeight⟩ }
  let mut placed : Array (Option Placeable) := .replicate children.size none
  let mut w := c.minWidth
  let mut h := c.minHeight
  for i in [0:children.size] do
    let m := children[i]!
    unless m.parentData.matchParentSize do
      let p ← m.measure c.loosen
      placed := placed.set! i (some p)
      w := max w p.width
      h := max h p.height
  let boxSize := c.constrain ⟨w, h⟩
  for i in [0:children.size] do
    if children[i]!.parentData.matchParentSize then
      placed := placed.set! i
        (some (← children[i]!.measure (Constraints.fixed boxSize.width boxSize.height)))
  return {
    size := boxSize
    placement := do
      for i in [0:children.size] do
        if let some p := placed[i]! then
          let a : Alignment := match children[i]!.parentData.align with
            | some (hb, vb) => ⟨hb, vb⟩
            | none => contentAlign
          p.placeAt (a.align p.size boxSize) }

/-- Stack children on top of each other (later children draw on top).
Mirrors `androidx.compose.foundation.layout.Box`. -/
def Box (content : Composable Unit := pure ())
    (modifier : Modifier := {})
    (contentAlignment : Alignment := .topStart) : Composable Unit :=
  Layout modifier (boxPolicy contentAlignment) content
    (policyInputs := some (mixKeys 0x426f78
      (mixKeys contentAlignment.horizontalBias.toBits.toUInt64
        contentAlignment.verticalBias.toBits.toUInt64)))

/-- Empty space, sized by its modifier (`Modifier.size`, `weight`, …).
Mirrors `androidx.compose.foundation.layout.Spacer`. -/
def Spacer (modifier : Modifier := {}) : Composable Unit :=
  Layout modifier .leaf (policyInputs := some 0x53706163)

/-! ## Intrinsic width -/

/-- Identity key of `Modifier.widthIntrinsicMax`'s layout block (it captures
nothing, so one process-wide key suffices). -/
private def widthIntrinsicMaxKey : UInt64 := 0x77496d78

namespace Modifier

/-- Fix the width to the content's **maximal intrinsic width**: size to the
widest child, then stretch fill-width children to exactly that width. Two
measure passes: a width-unbounded probe finds the content's natural width (a
`fillMaxWidth` child is a no-op on the unbounded axis, so the widest
wrap-content child wins), then the real pass re-measures with the width fixed
to the probe result clamped into the incoming constraints — the last
measurement defines the resolved geometry (see `CustomLayout`). Height
constraints pass through unchanged. This is how a dropdown menu wraps its
widest item while the items' hover rows still span the whole menu. Mirrors
`androidx.compose.foundation.layout.width(IntrinsicSize.Max)`. -/
def widthIntrinsicMax (m : Modifier := {}) : Modifier :=
  m.customLayout widthIntrinsicMaxKey
    { run := fun _ c inner => do
        if c.hasFixedWidth then
          return (← inner c, .zero)
        let natural ← inner { c with minWidth := 0, maxWidth := Constraints.infinity }
        let w := c.constrainWidth natural.width
        return (← inner { c with minWidth := w, maxWidth := w }, .zero) }

end Modifier

end Compose
