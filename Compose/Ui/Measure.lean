import Compose.Ui.Constraints
import Compose.Core.Density

namespace Compose

/-!
# Measure contract (`Compose/Ui/Measure.lean`)

Compose's single-pass layout protocol, SDL-free: a parent's `MeasurePolicy`
receives its children as `Measurable`s, measures each exactly once with the
constraints of its choosing (getting a `Placeable` back), decides its own
size, and returns a placement block that positions the placeables. Mirrors
`androidx.compose.ui.layout.{Measurable, Placeable, MeasureResult,
MeasurePolicy, MeasureScope}`.
-/

/-- The ambient context of a measure pass: carries the `Density` used to
resolve `Dp` to pixels at measure time. Mirrors
`androidx.compose.ui.layout.MeasureScope` (which is a `Density`). -/
structure MeasureScope where
  density : Density := {}
  deriving Repr, Inhabited

namespace MeasureScope

/-- Resolve a `Dp` to whole pixels. Mirrors `Density.roundToPx`. -/
def roundToPx (ms : MeasureScope) (dp : Dp) : Int32 := ms.density.dpRoundToPx dp

/-- Resolve a `Dp` to fractional pixels. Mirrors `Density.toPx`. -/
def toPx (ms : MeasureScope) (dp : Dp) : Float32 := ms.density.dpToPx dp

#guard ({ density := { density := 2.0 } : MeasureScope }).roundToPx 16 == 32
#guard ({ density := { density := 2.0 } : MeasureScope }).toPx 8 == 16.0

end MeasureScope

/-- A measured child: its chosen size plus the placement callback the parent's
placement block invokes to position it. Mirrors
`androidx.compose.ui.layout.Placeable` (+ `Placeable.PlacementScope.place`). -/
structure Placeable where
  width : Int32
  height : Int32
  /-- Position the child at `pos` in the parent's content coordinate space.
  Mirrors `Placeable.placeAt`. -/
  placeAt : IntOffset → IO Unit

namespace Placeable

/-- The measured size as an `IntSize`. -/
def size (p : Placeable) : IntSize := ⟨p.width, p.height⟩

end Placeable

/-- What a measure policy returns: the layout's chosen size and a deferred
placement block that places the children. Mirrors
`androidx.compose.ui.layout.MeasureResult`. -/
structure MeasureResult where
  size : IntSize
  placement : IO Unit := pure ()

/-- Per-child data a modifier communicates to the *parent's* measure policy
(Compose's `Measurable.parentData`, monomorphized: the union of the fields
our layouts consume instead of an `Any?`). Box alignment is stored as
`(horizontalBias, verticalBias)` in `[-1, 1]` (Compose's `BiasAlignment`). -/
structure ParentData where
  /-- `RowScope`/`ColumnScope` `weight`; `0` = unweighted. -/
  weight : Float32 := 0
  /-- Whether a weighted child must fill its allotted main-axis space
  (`min = max`). Mirrors the `fill` flag of `Modifier.weight`. -/
  fill : Bool := true
  /-- `BoxScope.align` override as alignment biases. -/
  align : Option (Float32 × Float32) := none
  /-- `BoxScope.matchParentSize`: measured with the box's final size. -/
  matchParentSize : Bool := false
  deriving Repr, BEq, Inhabited

/-- A child from the parent policy's point of view: measurable exactly once
per pass, exposing its modifier-provided parent data. Mirrors
`androidx.compose.ui.layout.Measurable`. -/
structure Measurable where
  /-- Measure with the given constraints, yielding a `Placeable`. -/
  measure : Constraints → IO Placeable
  parentData : ParentData := {}

/-- Panic/default value only (measures to zero); enables `!`-indexing of
measurable arrays in policies. -/
instance : Inhabited Measurable :=
  ⟨{ measure := fun _ => return { width := 0, height := 0, placeAt := fun _ => pure () } }⟩

/-- How a layout measures its children and places them: the heart of every
container. Mirrors `androidx.compose.ui.layout.MeasurePolicy` (the scope is
an explicit first argument rather than a receiver). -/
def MeasurePolicy := MeasureScope → Array Measurable → Constraints → IO MeasureResult

/-- The policy of a leaf `Layout`: children ignored, size = the smallest size
satisfying the constraints (modifiers like `Modifier.size` drive the minima).
Mirrors the empty-content `Layout` policy idiom. -/
def MeasurePolicy.leaf : MeasurePolicy := fun _ _ c =>
  return { size := ⟨c.minWidth, c.minHeight⟩ }

/-- The default policy of a fresh/root `LayoutNode`: measures every child with
the incoming constraints, places them at the origin, and sizes to the largest
child (clamped). This is what the applier's root node uses, mirroring the
root `LayoutNode` measure behavior. -/
def MeasurePolicy.root : MeasurePolicy := fun _ ms c => do
  let ps ← ms.mapM (·.measure c)
  let w := ps.foldl (fun acc p => max acc p.width) 0
  let h := ps.foldl (fun acc p => max acc p.height) 0
  return { size := c.constrain ⟨w, h⟩
           placement := ps.forM (·.placeAt .zero) }

instance : Inhabited MeasurePolicy := ⟨.leaf⟩

end Compose
