import Compose.Foundation.Scroll
import Compose.Ui.Layout
import Compose.Ui.Window

namespace Compose

/-!
# LazyColumn-lite and LazyGrid-lite (`Compose/Foundation/Lazy.lean`)

Fixed-item-size virtualization over the M10 scroll primitives — the
documented simplification of `androidx.compose.foundation.lazy.LazyColumn` /
`lazy.grid.LazyVerticalGrid` (every item has the stated fixed size; no
per-item measurement pass drives the window). Only the visible index window
(±`overscan` items) is composed, via `keyed`; in `LazyColumn` each item
additionally sits in its own restart scope that skips when its index is
unchanged — so scrolling composes exactly the *entering* items, disposes the
leaving ones, and keeps the state of survivors.

The scroll position itself never recomposes anything: items are placed at
`index × itemSize` inside a content block whose total extent is
`count × itemSize`, and the scroll modifiers offset that block during
*measurement*. Recomposition happens only when the visible window shifts
(a `derivedStateOf` over the scroll value/viewport, invalidating readers only
when the window pair actually changes).

`LazyGrid` virtualizes both axes at once (the M13b Cells pattern, promoted in
M14b): per axis either a shared `ScrollState` (scrolling, windowed) or `none`
(pinned, fully composed) — so a spreadsheet grid, its sticky header strips,
and a plain lazy row are all the same component.
-/

/-- The composed index window for a lazy column: `[first, lastEx)` with
`overscan` extra items on each side, clamped to `[0, count)`. `viewport = 0`
(before the first measure) still yields the leading items. -/
def lazyWindow (value viewport : Float32) (itemPx : Int32) (count : Nat)
    (overscan : Nat := 1) : Nat × Nat :=
  if itemPx ≤ 0 || count == 0 then (0, 0) else
  let h := itemPx.toFloat32
  let v := max value 0
  let firstVisible := (v / h).floor.toUInt32.toNat
  let lastVisible := ((v + max viewport 0) / h).ceil.toUInt32.toNat
  let first := min (firstVisible - min firstVisible overscan) count
  let lastEx := min (max lastVisible (firstVisible + 1) + overscan) count
  (first, max lastEx first)

#guard lazyWindow 0 100 20 100 == (0, 6)          -- 5 visible + 1 overscan below
#guard lazyWindow 100 100 20 100 == (4, 11)       -- items 5..9 visible, ±1
#guard lazyWindow 110 100 20 100 == (4, 12)       -- straddling rows both ends
#guard lazyWindow 1900 100 20 100 == (94, 100)    -- clamped at the tail
#guard lazyWindow 0 100 20 3 == (0, 3)            -- fewer items than fit
#guard lazyWindow 0 0 20 100 == (0, 2)            -- pre-measure viewport 0
#guard lazyWindow 0 100 20 0 == (0, 0)
#guard lazyWindow (-5) 100 20 100 == (0, 6)       -- defensive negative value

/-- One lazy item's restart scope: skips (body not re-run) when the scope is
valid and the item index is unchanged — the wrapper recomposing on a window
shift re-composes only entering items. The content lambda is deliberately
not part of the skip check (Compose's stable-lambda assumption). -/
private partial def lazyItem (i : Nat) (body : Nat → Composable Unit) :
    Composable Unit := fun c => do
  let scope ← c.startRestartGroup (stringKey "Compose.Foundation.LazyColumn.item")
  let cell ← c.remember (IO.mkRef i)
  let old ← cell.get
  cell.set i
  if ← c.shouldSkip scope (argsChanged := old != i) then
    c.skipToGroupEnd
  else
    (body i).run c
  c.endRestartGroup scope ((lazyItem i body).run c)

/-- The lazy content's measure policy: children are the composed window
(indices `first..`), each measured exactly `itemPx` tall, placed at
`index × itemPx`; the reported height is the *full* `count × itemPx`, so the
enclosing scroll sees the whole virtual extent. -/
private def lazyPolicy (first count : Nat) (itemPx : Int32) : MeasurePolicy :=
  fun _ ms c => do
    let ps ← ms.mapM (·.measure
      { maxWidth := c.maxWidth, minHeight := itemPx, maxHeight := itemPx })
    let w := ps.foldl (fun acc p => max acc p.width) 0
    return { size := ⟨c.constrainWidth w, c.constrainHeight (itemPx * Int32.ofNat count)⟩
             placement := do
               let mut j := 0
               for p in ps do
                 p.placeAt ⟨0, itemPx * Int32.ofNat (first + j)⟩
                 j := j + 1 }

/-- A vertically scrolling, virtualized column of `count` fixed-height items:
only the visible window (±1 item) is composed; items are identified by
`key` (state survives scrolling while an item stays in the window); works
with `ScrollState` (wheel, scrollbar, `scrollTo`/`animateScrollTo`).
`itemContent i` composes item `i`. Mirrors
`androidx.compose.foundation.lazy.LazyColumn` (fixed-height simplification —
see the module docstring). -/
composable def LazyColumn (state : ScrollState) (itemHeight : Dp) (count : Nat)
    (itemContent : Nat → Composable Unit := fun _ => pure ())
    (key : Nat → UInt64 := (·.toUInt64)) (modifier : Modifier := {}) :
    Composable Unit := do
  let density ← LocalDensity.current
  let itemPx := density.dpRoundToPx itemHeight
  -- The window derives from scroll value + viewport; readers (this scope)
  -- are invalidated only when the (first, lastEx) pair actually changes.
  let windowState ← rememberDerivedKeyed (α := Nat × Nat)
    (mixKeys itemPx.toFloat32.toBits.toUInt64 count.toUInt64) do
      return lazyWindow (← state.value) (← state.viewportSize) itemPx count
  let (first, lastEx) ← windowState.get
  Layout (modifier.verticalScroll state) (lazyPolicy first count itemPx)
    (policyInputs := some (mixKeys 0x6c617a79 <| mixKeys first.toUInt64 <|
      mixKeys count.toUInt64 itemPx.toFloat32.toBits.toUInt64)) do
    for i in [first:lastEx] do
      keyed (key i) (lazyItem i itemContent)

/-! ## LazyGrid -/

/-- The lazy grid's measure policy: children are the composed cell window,
each measured at exactly `cw × ch` px and placed row-major into the
`cols`-wide window starting at cell `(c0, r0)`; the reported size is the
*full* virtual extent (`columns × rows` cells), so enclosing scroll modifiers
see the whole sheet. A pinned header strip is just the 1-high/1-wide case. -/
private def lazyGridPolicy (c0 r0 cols columns rows : Nat) (cw ch : Int32) :
    MeasurePolicy := fun _ ms c => do
  let ps ← ms.mapM (·.measure (Constraints.fixed cw ch))
  return { size := c.constrain ⟨cw * Int32.ofNat columns, ch * Int32.ofNat rows⟩
           placement := do
             if cols == 0 then return
             let mut j := 0
             for p in ps do
               p.placeAt ⟨cw * Int32.ofNat (c0 + j % cols),
                          ch * Int32.ofNat (r0 + j / cols)⟩
               j := j + 1 }

/-- A stable hash of a lazy grid's window + cell geometry (policy inputs). -/
private def lazyGridKey (c0 c1 r0 r1 : Nat) (cw ch : Int32) : UInt64 :=
  mixKeys c0.toUInt64 <| mixKeys c1.toUInt64 <| mixKeys r0.toUInt64 <|
    mixKeys r1.toUInt64 <|
      mixKeys cw.toFloat32.toBits.toUInt64 ch.toFloat32.toBits.toUInt64

/-- A 2-axis virtualized grid of `columns × rows` fixed-size cells: only the
visible cell window (±1 cell per scrolling axis) is composed, each cell under
`keyed` (state survives while it stays in the window). Per axis, pass a
`ScrollState` to make it scroll (wheel, scrollbar, `scrollTo`; the state may
be shared with other grids — sticky headers are 1-axis grids sharing the main
grid's state) or `none` to pin it (that axis composes fully). `itemContent
col row` composes one cell; `contentModifier` lands *inside* the scroll
wrappers, so its pointer handlers see content-local positions (grid-level tap
detection), while `modifier` stays outside (tags, focus, keys, sizing).
Mirrors `androidx.compose.foundation.lazy.grid.LazyVerticalGrid` /
`LazyHorizontalGrid`, collapsed to the fixed-cell-size 2-axis case. -/
composable def LazyGrid (columns rows : Nat) (cellWidth cellHeight : Dp)
    (itemContent : Nat → Nat → Composable Unit := fun _ _ => pure ())
    (hState vState : Option ScrollState := none)
    (modifier : Modifier := {}) (contentModifier : Modifier := {})
    (key : Nat → Nat → UInt64 := fun c r => (r * columns + c).toUInt64) :
    Composable Unit := do
  let density ← LocalDensity.current
  let cw := density.dpRoundToPx cellWidth
  let ch := density.dpRoundToPx cellHeight
  let sizeKey := mixKeys cw.toFloat32.toBits.toUInt64 ch.toFloat32.toBits.toUInt64
  -- Per-axis window: lazily derived on a scrolling axis, the full range on a
  -- pinned one. Readers wake only when a window pair actually changes.
  let win ← rememberDerivedKeyed (α := (Nat × Nat) × Nat × Nat) sizeKey do
    let axis (state? : Option ScrollState) (itemPx : Int32) (count : Nat) :
        IO (Nat × Nat) := do
      match state? with
      | some s => return lazyWindow (← s.value) (← s.viewportSize) itemPx count
      | none => return (0, count)
    return (← axis hState cw columns, ← axis vState ch rows)
  let ((c0, c1), r0, r1) ← win.get
  let m := match hState with | some s => modifier.horizontalScroll s | none => modifier
  let m := match vState with | some s => m.verticalScroll s | none => m
  Layout (m.then contentModifier) (lazyGridPolicy c0 r0 (c1 - c0) columns rows cw ch)
    (policyInputs := some (mixKeys 0x6c677269 (lazyGridKey c0 c1 r0 r1 cw ch))) do
    for r in [r0:r1] do
      for c in [c0:c1] do
        keyed (key c r) (itemContent c r)

end Compose
