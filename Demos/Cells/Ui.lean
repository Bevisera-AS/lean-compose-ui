import Compose
import Demos.Cells.Engine

/-!
# Cells UI (`lake exe demo-cells`)

The 7GUIs **Cells** demo: a scrollable 26×99 spreadsheet (columns `A`–`Z`,
rows `1`–`99`) over the pure formula engine in `Demos/Cells/Engine.lean`.

* **2-axis virtualization**: the cell area is a `LazyGrid` over two
  `ScrollState`s (one per axis) — only the visible cell window composes,
  while the grid reports the *full* sheet extent to the framework scroll
  containers (clipping, wheel handling, offset placement).
* **Sticky headers**: the column-header row and row-header column are 1-axis
  `LazyGrid`s sharing the cell grid's scroll state on their scrolling axis —
  pinned on the other. The corner cell is a plain box, pinned both ways.
* **Editing**: click selects (committing any open edit), double-click or
  `Enter` opens an editor (`TextField` seeded with the cell's *source*),
  typing starts an edit that replaces the content. `Enter` commits (the
  engine recomputes dependents incrementally), `Esc` cancels, `Delete`
  clears the selected cell, arrows move the selection (auto-scrolled into
  view). Errors and cycles display their engine code (`#CYCLE!`, …) in the
  error color.
* **Scrollbars**: the Material `VerticalScrollbar` + `HorizontalScrollbar`
  overlaid on the grid's end/bottom edges.

Headless smoke: `SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe
demo-cells`.
-/

namespace Demos.Cells

open Compose Compose.Draw

/-! ## Grid geometry (pure) -/

/-- Number of columns (`A`–`Z`). -/
def colCount : Nat := 26

/-- Number of rows (`1`–`99`). -/
def rowCount : Nat := 99

/-- Cell width. -/
def cellW : Dp := 80

/-- Cell height. -/
def cellH : Dp := 28

/-- Width of the pinned row-header column. -/
def headerW : Dp := 36

/-- Height of the pinned column-header row. -/
def headerH : Dp := 28

/-- The cell under a grid-content-local position (`cwPx`/`chPx` = cell size
in px), clamped into the sheet — the whole hit test of the grid's single
tap detector. -/
def refAt (pos : Offset) (cwPx chPx : Float32) : CellRef :=
  if cwPx ≤ 0 || chPx ≤ 0 then ⟨0, 1⟩ else
  ⟨min (colCount - 1) ((max pos.x 0) / cwPx).floor.toUInt32.toNat,
   min rowCount (((max pos.y 0) / chPx).floor.toUInt32.toNat + 1)⟩

#guard refAt ⟨0, 0⟩ 80 28 == ⟨0, 1⟩
#guard refAt ⟨79, 27⟩ 80 28 == ⟨0, 1⟩          -- last px still the first cell
#guard refAt ⟨80, 28⟩ 80 28 == ⟨1, 2⟩          -- first px of the next
#guard refAt ⟨99999, 99999⟩ 80 28 == ⟨25, 99⟩  -- clamped bottom-right
#guard refAt ⟨-5, -5⟩ 80 28 == ⟨0, 1⟩          -- clamped top-left
#guard refAt ⟨205, 0⟩ 80 28 == ⟨2, 1⟩

/-- The scroll offset that brings `[start, start+size)` into the viewport
`[value, value+viewport)`: unchanged when already visible, else the nearest
edge (the arrow-key auto-scroll math). -/
def scrollIntoView (start size value viewport : Float32) : Float32 :=
  if start < value then start
  else if start + size > value + viewport then start + size - viewport
  else value

#guard scrollIntoView 0 28 100 200 == 0        -- above: snap to its top
#guard scrollIntoView 400 28 100 200 == 228    -- below: snap to its bottom
#guard scrollIntoView 150 28 100 200 == 100    -- visible: unchanged
#guard scrollIntoView 100 28 100 200 == 100    -- exactly at the top edge
#guard scrollIntoView 272 28 100 200 == 100    -- exactly at the bottom edge

/-- Move a reference by `(dc, dr)` columns/rows, clamped into the sheet —
arrow-key selection movement. -/
def moveRef (r : CellRef) (dc dr : Int) : CellRef :=
  ⟨min (colCount - 1) ((r.col : Int) + dc).toNat,
   min rowCount (max 1 (((r.row : Int) + dr).toNat))⟩

#guard moveRef ⟨3, 5⟩ (-1) 2 == ⟨2, 7⟩
#guard moveRef ⟨0, 1⟩ (-1) 0 == ⟨0, 1⟩         -- clamped at A
#guard moveRef ⟨0, 1⟩ 0 (-1) == ⟨0, 1⟩         -- clamped at row 1
#guard moveRef ⟨25, 99⟩ 1 1 == ⟨25, 99⟩        -- clamped at Z99
#guard moveRef ⟨0, 1⟩ 30 200 == ⟨25, 99⟩

/-- Column label (`0 ⇒ "A"`). -/
def colLabel (c : Nat) : String := s!"{Char.ofNat (65 + c)}"

#guard colLabel 0 == "A"
#guard colLabel 25 == "Z"

/-! ## Demo state -/

/-- Everything the Cells screen remembers: the reactive sheet, the selected
cell, the cell being edited (if any), and the editor's draft text. The draft
lives here (not inside the `TextField`) so commits triggered from outside
the field — `Enter` on the grid, click-away — see the latest text. -/
structure CellsState where
  /-- The spreadsheet (always-notify policy: `Sheet` has no useful `BEq`). -/
  sheet : MutableState Sheet
  /-- The selected cell (always exactly one). -/
  selected : MutableState CellRef
  /-- The cell whose editor is open, if any. -/
  editing : MutableState (Option CellRef)
  /-- The editor's current text. -/
  draft : MutableState String

instance : Nonempty CellsState :=
  ⟨{ sheet := Classical.choice inferInstance
     selected := Classical.choice inferInstance
     editing := Classical.choice inferInstance
     draft := Classical.choice inferInstance }⟩

/-- The sheet the interactive demo boots with — a little dependency chain so
the first paint already shows formulas at work. -/
def seedSheet : Sheet :=
  [((⟨0, 1⟩ : CellRef), "10"), (⟨0, 2⟩, "20"), (⟨0, 3⟩, "30"),
   (⟨0, 5⟩, "=SUM(A1:A3)"), (⟨1, 5⟩, "=A5*2"), (⟨1, 1⟩, "hello")]
  |>.foldl (fun s (ref, inp) => s.set ref inp) Sheet.empty

/-- Fresh screen state over `initial`. -/
def CellsState.create (initial : Sheet := seedSheet) : IO CellsState :=
  return { sheet := ← MutableState.createAlwaysNotify initial
           selected := ← MutableState.create (⟨0, 1⟩ : CellRef)
           editing := ← MutableState.create (none : Option CellRef)
           draft := ← MutableState.create "" }

namespace CellsState

/-- Commit the open editor: feed the draft to the engine (`Sheet.set`
recomputes exactly the dirty closure) and close the editor. No-op when
nothing is being edited. -/
def commit (st : CellsState) : IO Unit := do
  if let some ref ← st.editing.cell.get then
    st.sheet.set ((← st.sheet.cell.get).set ref (← st.draft.cell.get))
    st.editing.set none

/-- Close the editor without committing. -/
def cancelEdit (st : CellsState) : IO Unit :=
  st.editing.set none

/-- Select `ref`, committing any open edit first (spreadsheet click-away). -/
def select (st : CellsState) (ref : CellRef) : IO Unit := do
  st.commit
  st.selected.set ref

/-- Open the editor on `ref`, seeded with the cell's *source*
(`Sheet.sourceOf`, so formulas re-edit as typed). A pending edit of another
cell commits first; re-opening the edited cell keeps the draft. -/
def openEditor (st : CellsState) (ref : CellRef) : IO Unit := do
  unless (← st.editing.cell.get) == some ref do
    st.commit
    st.selected.set ref
    st.draft.set ((← st.sheet.cell.get).sourceOf ref)
    st.editing.set (some ref)

/-- Committed text typed while the *grid* holds focus: extends the open
draft, or starts an edit that **replaces** the selected cell's content
(spreadsheet type-to-edit). Always consumes. -/
def typeInto (st : CellsState) (t : String) : IO Bool := do
  match ← st.editing.cell.get with
  | some _ => st.draft.modify (· ++ t)
  | none =>
    st.draft.set t
    st.editing.set (some (← st.selected.cell.get))
  return true

/-- Clear `ref` (commit an empty input through the engine). -/
def clearCell (st : CellsState) (ref : CellRef) : IO Unit := do
  st.sheet.set ((← st.sheet.cell.get).set ref "")

/-- The grid's key handler (also receives `Enter`/`Esc` bubbling out of a
focused cell editor, which consumes everything else it cares about):
`Enter` commits or opens the editor, `Esc` cancels, `Delete` clears,
`Backspace` trims a grid-focused draft, arrows move the selection and
auto-scroll it into view. -/
def onKey (st : CellsState) (hs vs : ScrollState) (cwPx chPx : Float32)
    (ke : KeyEvent) : IO Bool := do
  if !ke.down then return false
  let editing ← st.editing.cell.get
  let moveSel (dc dr : Int) : IO Bool := do
    if editing.isSome then return false
    let r := moveRef (← st.selected.cell.get) dc dr
    st.selected.set r
    hs.scrollTo (scrollIntoView (r.col.toFloat32 * cwPx) cwPx
      (← hs.valueState.cell.get) (← hs.viewportSizeState.cell.get))
    vs.scrollTo (scrollIntoView ((r.row - 1).toFloat32 * chPx) chPx
      (← vs.valueState.cell.get) (← vs.viewportSizeState.cell.get))
    return true
  match ke.key with
  | .«return» =>
    if editing.isSome then st.commit
    else st.openEditor (← st.selected.cell.get)
    return true
  | .escape =>
    if editing.isSome then st.cancelEdit; return true
    else return false                      -- fall through: Esc clears focus
  | .backspace =>
    if editing.isSome then
      st.draft.modify (fun s => String.ofList s.toList.dropLast)
      return true
    else return false
  | .delete =>
    if editing.isNone then st.clearCell (← st.selected.cell.get); return true
    else return false
  | .left => moveSel (-1) 0
  | .right => moveSel 1 0
  | .up => moveSel 0 (-1)
  | .down => moveSel 0 1
  | _ => return false

end CellsState

/-! ## Grid pieces -/

/-- 1-px grid lines on a cell's right and bottom edges (drawn per cell so
adjacent cells share a single line). -/
private def gridLineDraw (c : Color) : DrawM Unit := do
  let sz ← DrawScope.size
  DrawScope.drawRect (.solid c) ⟨sz.width - 1, 0⟩ ⟨1, sz.height⟩
  DrawScope.drawRect (.solid c) ⟨0, sz.height - 1⟩ ⟨sz.width, 1⟩

/-- One header cell (column letter or row number), highlighted when its
column/row holds the selection. -/
composable def headerCell (tag label : String) (highlight : Bool) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Box (modifier := Modifier.semantics (testTag := some tag) (mergeDescendants := true)
        |>.background (if highlight then colors.primaryContainer
                       else colors.surfaceVariant)
        |>.drawBehind (gridLineDraw colors.outlineVariant))
    (contentAlignment := .center)
    (Text label (style := { fontSize := 12 })
      (color := some colors.onSurfaceVariant))

/-- The pinned column-header row (`A`–`Z`): a 1-row `LazyGrid` sharing the
grid's horizontal scroll state, so it follows the grid exactly while staying
vertically pinned. -/
composable def columnHeaders (st : CellsState) (hs : ScrollState) :
    Composable Unit := do
  let selCol := (← st.selected.get).col
  LazyGrid (columns := colCount) (rows := 1)
    (cellWidth := cellW) (cellHeight := headerH) (hState := some hs)
    (modifier := Modifier.height headerH)
    fun ci _ =>
      headerCell s!"colh-{colLabel ci}" (colLabel ci) (ci == selCol)

/-- The pinned row-header column (`1`–`99`): the vertical counterpart of
`columnHeaders`, a 1-column `LazyGrid` sharing the grid's vertical scroll
state. -/
composable def rowHeaders (st : CellsState) (vs : ScrollState)
    (modifier : Modifier := {}) : Composable Unit := do
  let selRow := (← st.selected.get).row
  LazyGrid (columns := 1) (rows := rowCount)
    (cellWidth := headerW) (cellHeight := cellH) (vState := some vs)
    (modifier := modifier)
    fun _ ri =>
      headerCell s!"rowh-{ri + 1}" s!"{ri + 1}" (ri + 1 == selRow)

/-- One grid cell. Editing cells host the editor (`TextField` over the
shared draft, tagged `cell-editor`); resting cells render `Sheet.displayOf`
with a selection background/outline, grid lines, and the error color for
`#CYCLE!`/`#ERR!`/… values. Tagged `cell-{ref}` with its selection state
published for the MT tests. -/
composable def cellView (st : CellsState) (ref : CellRef) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let ed ← st.editing.get
  if ed == some ref then
    TextField (← st.draft.get) st.draft.set
      (modifier := Modifier.testTag "cell-editor")
      (textStyle := { fontSize := 12 })
  else
    let isSel := (← st.selected.get) == ref
    let value := (← st.sheet.get).get ref
    let isErr := value matches .error _
    let base := Modifier.semantics (testTag := some s!"cell-{ref}")
        (selected := some isSel) (mergeDescendants := true)
      |>.background (if isSel then colors.primaryContainer else colors.surface)
      |>.drawBehind (gridLineDraw colors.outlineVariant)
    Box (modifier := if isSel then base.border 2 colors.primary else base)
      (contentAlignment := .centerStart)
      (Text value.display (modifier := Modifier.padding (horizontal := some 6))
        (style := { fontSize := 12 })
        (color := some (if isErr then colors.error else colors.onSurface)))

/-- The scrolling cell area: a `LazyGrid` on both scroll states, composing
only the visible cell window while reporting the full sheet extent. One
grid-level tap detector rides `contentModifier` — inside the scroll
wrappers, so its positions are content-local — turning taps into selection
and double-taps into editing via `refAt`; the grid is focusable and a
text-input client, so keys and typing work without clicking a cell editor
first. -/
composable def gridCells (st : CellsState) (hs vs : ScrollState) :
    Composable Unit := do
  let density ← LocalDensity.current
  let cwF := (density.dpRoundToPx cellW).toFloat32
  let chF := (density.dpRoundToPx cellH).toFloat32
  let sizeKey := mixKeys cwF.toBits.toUInt64 chF.toBits.toUInt64
  LazyGrid (columns := colCount) (rows := rowCount)
    (cellWidth := cellW) (cellHeight := cellH)
    (hState := some hs) (vState := some vs)
    (modifier := Modifier.testTag "grid"
      |>.focusable
      |>.onKeyEvent (st.onKey hs vs cwF chF)
      |>.onTextInput st.typeInto)
    (contentModifier := Modifier.pointerInput
      (mixKeys (stringKey "Demos.Cells.grid") sizeKey)
      (detectTapGestures
        (onTap := some fun p => st.select (refAt p cwF chF))
        (onDoubleTap := some fun p => st.openEditor (refAt p cwF chF))))
    (key := fun ci ri => ((ri + 1) * 26 + ci).toUInt64)
    fun ci ri => cellView st ⟨ci, ri + 1⟩

/-! ## The screen -/

/-- The formula bar: the selected reference and its source (the live draft
while editing) — the always-visible answer to "what is really in this
cell?". -/
composable def formulaBar (st : CellsState) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let sel ← st.selected.get
  let ed ← st.editing.get
  let src ← match ed with
    | some _ => st.draft.get
    | none => do pure ((← st.sheet.get).sourceOf sel)
  Row (modifier := Modifier.fillMaxWidth |>.background colors.surfaceVariant
        |>.padding (horizontal := some 8) (vertical := some 5))
      (horizontalArrangement := .spacedBy 8)
      (verticalAlignment := .centerVertically) do
    Text (toString sel) (modifier := Modifier.testTag "formula-ref" |>.width 32)
      (style := { fontSize := 12 }) (color := some colors.primary)
    Text src (modifier := Modifier.testTag "formula-src")
      (style := { fontSize := 12 })

/-- The assembled screen: formula bar on top; below it the pinned corner +
column headers, the pinned row headers, and the scrolling cell grid with
both scrollbars overlaid. -/
composable def cellsScreen (st : CellsState) (hs vs : ScrollState) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Column (modifier := Modifier.fillMaxSize |>.background colors.surface) do
    formulaBar st
    Row (modifier := Modifier.weight 1 |>.fillMaxWidth) do
      Column (modifier := Modifier.width headerW) do
        Box (modifier := Modifier.size headerW headerH |>.testTag "corner"
              |>.background colors.surfaceVariant
              |>.drawBehind (gridLineDraw colors.outlineVariant))
        rowHeaders st vs (Modifier.weight 1 |>.fillMaxWidth)
      Column (modifier := Modifier.weight 1 |>.fillMaxHeight) do
        columnHeaders st hs
        Box (modifier := Modifier.weight 1 |>.fillMaxWidth) do
          gridCells st hs vs
          VerticalScrollbar vs
            (Modifier.align .centerEnd |>.fillMaxHeight |>.testTag "vscrollbar")
          HorizontalScrollbar hs
            (Modifier.align .bottomCenter |>.fillMaxWidth |>.testTag "hscrollbar")

/-- The Cells demo UI (see the module docstring). `initial` seeds the sheet
(tests boot it empty). -/
composable def cellsUi (initial : Sheet := seedSheet) : Composable Unit := do
  let st ← remember (CellsState.create initial)
  let hs ← rememberScrollState
  let vs ← rememberScrollState
  cellsScreen st hs vs

end Demos.Cells
