import Compose.Foundation.Scroll
import Compose.Ui.Layout
import Compose.Ui.Window

namespace Compose

/-!
# LazyColumn-lite (`Compose/Foundation/Lazy.lean`)

Fixed-item-height vertical virtualization over the M10 scroll primitives —
the documented simplification of `androidx.compose.foundation.lazy.LazyColumn`
(every item is `itemHeight` tall; no per-item measurement pass drives the
window). Only the visible index window (±`overscan` items) is composed, via
`keyed`, and each item sits in its own restart scope that skips when its
index is unchanged — so scrolling composes exactly the *entering* items,
disposes the leaving ones, and keeps the state of survivors.

The scroll position itself never recomposes anything: items are placed at
`index × itemHeight` inside a content block whose total height is
`count × itemHeight`, and `Modifier.verticalScroll` offsets that block during
*measurement*. Recomposition happens only when the visible window shifts
(a `derivedStateOf` over the scroll value/viewport, invalidating readers only
when the `(first, last)` pair actually changes).
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
    (key : Nat → UInt64 := (·.toUInt64)) (modifier : Modifier := {})
    (itemContent : Nat → Composable Unit := fun _ => pure ()) : Composable Unit := do
  let density ← LocalDensity.current
  let itemPx := density.dpRoundToPx itemHeight
  -- The window derives from scroll value + viewport; readers (this scope)
  -- are invalidated only when the (first, lastEx) pair actually changes.
  let windowState ← rememberKeyed (mixKeys itemPx.toFloat32.toBits.toUInt64 count.toUInt64)
    (derivedStateOf (α := Nat × Nat) do
      return lazyWindow (← state.value) (← state.viewportSize) itemPx count)
  let (first, lastEx) ← windowState.get
  Layout (modifier.verticalScroll state) (lazyPolicy first count itemPx)
    (policyInputs := some (mixKeys 0x6c617a79 <| mixKeys first.toUInt64 <|
      mixKeys count.toUInt64 itemPx.toFloat32.toBits.toUInt64))
    (content := do
      for i in [first:lastEx] do
        keyed (key i) (lazyItem i itemContent))

end Compose
