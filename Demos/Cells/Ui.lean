import Compose
import Demos.Cells.Engine

/-!
# Cells UI (`lake exe demo-cells`)

The 7GUIs **Cells** demo: a scrollable 26×99 spreadsheet (columns `A`–`Z`,
rows `1`–`99`) over the pure formula engine in `Demos/Cells/Engine.lean`.

* **2-axis virtualization**: only the visible cell window composes. Two
  `ScrollState`s (one per axis) drive `lazyWindow`-derived index windows;
  the grid is a single `Layout` that reports the *full* content size inside
  `Modifier.horizontalScroll |>.verticalScroll`, so the framework scroll
  containers own clipping, wheel handling, and offset placement.
* **Sticky headers**: the column-header row and row-header column are
  independent virtualized strips sharing the grid's scroll states on their
  one scrolling axis — pinned on the other. The corner cell is a plain box,
  pinned both ways.
* **Editing**: click selects (committing any open edit), double-click or
  `Enter` opens an editor (`TextFieldS` seeded with the cell's *source*),
  typing starts an edit that replaces the content. `Enter` commits (the
  engine recomputes dependents incrementally), `Esc` cancels, `Delete`
  clears the selected cell, arrows move the selection (auto-scrolled into
  view). Errors and cycles display their engine code (`#CYCLE!`, …) in the
  error color.
* **Scrollbars**: the Material `VerticalScrollbar` plus a demo-local
  horizontal variant (an M14 promotion candidate — see `HorizontalScrollbar`).

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
lives here (not inside the `TextFieldS`) so commits triggered from outside
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
  return { sheet := ← mutableStateOfAlwaysNotify initial
           selected := ← mutableStateOf (⟨0, 1⟩ : CellRef)
           editing := ← mutableStateOf (none : Option CellRef)
           draft := ← mutableStateOf "" }

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

/-- Measure policy of a virtualized strip (headers) or the cell grid:
children measure at exactly `iw × ih` px and land row-major into the
`cols`-wide index window starting at `(c0, r0)`; the reported size is the
*full* virtual extent (`countW × countH` cells), so the enclosing scroll
modifiers see the whole sheet. A strip is just the 1-high/1-wide case. -/
private def gridPolicy (c0 r0 cols countW countH : Nat) (iw ih : Int32) :
    MeasurePolicy := fun _ ms c => do
  let ps ← ms.mapM (·.measure (Constraints.fixed iw ih))
  return { size := c.constrain ⟨iw * Int32.ofNat countW, ih * Int32.ofNat countH⟩
           placement := do
             if cols == 0 then return
             let mut j := 0
             for p in ps do
               p.placeAt ⟨iw * Int32.ofNat (c0 + j % cols),
                          ih * Int32.ofNat (r0 + j / cols)⟩
               j := j + 1 }

/-- A stable hash for a policy's window/geometry inputs. -/
private def windowKey (a b c : Nat) (iw ih : Int32) : UInt64 :=
  mixKeys a.toUInt64 <| mixKeys b.toUInt64 <| mixKeys c.toUInt64 <|
    mixKeys iw.toFloat32.toBits.toUInt64 ih.toFloat32.toBits.toUInt64

/-- One header cell (column letter or row number), highlighted when its
column/row holds the selection. -/
composable def headerCell (tag label : String) (highlight : Bool) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Box (Modifier.semantics (testTag := some tag) (mergeDescendants := true)
        |>.background (if highlight then colors.primaryContainer
                       else colors.surfaceVariant)
        |>.drawBehind (gridLineDraw colors.outlineVariant))
    (contentAlignment := .center)
    (content := fun _ =>
      Text label (style := { fontSize := 12 })
        (color := some colors.onSurfaceVariant))

/-- The pinned column-header row (`A`–`Z`): a horizontal virtualized strip
sharing the grid's horizontal scroll state, so it follows the grid exactly
while staying vertically pinned. -/
composable def columnHeaders (st : CellsState) (hs : ScrollState) :
    Composable Unit := do
  let density ← LocalDensity.current
  let cwPx := density.dpRoundToPx cellW
  let hhPx := density.dpRoundToPx headerH
  let win ← rememberKeyed cwPx.toFloat32.toBits.toUInt64
    (derivedStateOf (α := Nat × Nat) do
      return lazyWindow (← hs.value) (← hs.viewportSize) cwPx colCount)
  let (c0, c1) ← win.get
  let selCol := (← st.selected.get).col
  Layout (Modifier.height headerH |>.horizontalScroll hs)
    (gridPolicy c0 0 (c1 - c0) colCount 1 cwPx hhPx)
    (policyInputs := some (mixKeys 0x63686472 (windowKey c0 c1 0 cwPx hhPx)))
    (content := do
      for ci in [c0:c1] do
        keyed ci (headerCell s!"colh-{colLabel ci}" (colLabel ci) (ci == selCol)))

/-- The pinned row-header column (`1`–`99`): the vertical counterpart of
`columnHeaders`, sharing the grid's vertical scroll state. -/
composable def rowHeaders (st : CellsState) (vs : ScrollState)
    (modifier : Modifier := {}) : Composable Unit := do
  let density ← LocalDensity.current
  let chPx := density.dpRoundToPx cellH
  let hwPx := density.dpRoundToPx headerW
  let win ← rememberKeyed chPx.toFloat32.toBits.toUInt64
    (derivedStateOf (α := Nat × Nat) do
      return lazyWindow (← vs.value) (← vs.viewportSize) chPx rowCount)
  let (r0, r1) ← win.get
  let selRow := (← st.selected.get).row
  Layout (modifier.verticalScroll vs)
    (gridPolicy 0 r0 1 1 rowCount hwPx chPx)
    (policyInputs := some (mixKeys 0x72686472 (windowKey r0 r1 0 hwPx chPx)))
    (content := do
      for ri in [r0:r1] do
        keyed ri (headerCell s!"rowh-{ri + 1}" s!"{ri + 1}" (ri + 1 == selRow)))

/-- One grid cell. Editing cells host the editor (`TextFieldS` over the
shared draft, tagged `cell-editor`); resting cells render `Sheet.displayOf`
with a selection background/outline, grid lines, and the error color for
`#CYCLE!`/`#ERR!`/… values. Tagged `cell-{ref}` with its selection state
published for the MT tests. -/
composable def cellView (st : CellsState) (ref : CellRef) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let ed ← st.editing.get
  if ed == some ref then
    TextFieldS (← st.draft.get) st.draft.set
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
    Box (if isSel then base.border 2 colors.primary else base)
      (contentAlignment := .centerStart)
      (content := fun _ =>
        Text value.display (modifier := Modifier.padding (horizontal := some 6))
          (style := { fontSize := 12 })
          (color := some (if isErr then colors.error else colors.onSurface)))

/-- The scrolling cell area: a single `Layout` composing only the visible
cell window (derived from both scroll states), reporting the full sheet
extent inside `horizontalScroll |>.verticalScroll`. One grid-level pointer
detector — placed *inside* the scroll wrappers, so its positions are
content-local — turns taps into selection and double-taps into editing via
`refAt`; the grid is focusable and a text-input client, so keys and typing
work without a programmatic focus API. -/
composable def gridCells (st : CellsState) (hs vs : ScrollState) :
    Composable Unit := do
  let density ← LocalDensity.current
  let cwPx := density.dpRoundToPx cellW
  let chPx := density.dpRoundToPx cellH
  let sizeKey := mixKeys cwPx.toFloat32.toBits.toUInt64 chPx.toFloat32.toBits.toUInt64
  let win ← rememberKeyed sizeKey
    (derivedStateOf (α := (Nat × Nat) × Nat × Nat) do
      return (lazyWindow (← hs.value) (← hs.viewportSize) cwPx colCount,
              lazyWindow (← vs.value) (← vs.viewportSize) chPx rowCount))
  let ((c0, c1), r0, r1) ← win.get
  let cwF := cwPx.toFloat32
  let chF := chPx.toFloat32
  let m := Modifier.testTag "grid"
    |>.focusable
    |>.onKeyEvent (st.onKey hs vs cwF chF)
    |>.onTextInput st.typeInto
    |>.horizontalScroll hs
    |>.verticalScroll vs
    |>.pointerInput (mixKeys (stringKey "Demos.Cells.grid") sizeKey)
        (detectTapGestures
          (onTap := some fun p => st.select (refAt p cwF chF))
          (onDoubleTap := some fun p => st.openEditor (refAt p cwF chF)))
  Layout m (gridPolicy c0 r0 (c1 - c0) colCount rowCount cwPx chPx)
    (policyInputs := some (mixKeys 0x67726964 <|
      mixKeys (windowKey c0 c1 r0 cwPx chPx) r1.toUInt64))
    (content := do
      for ri in [r0:r1] do
        for ci in [c0:c1] do
          keyed ((ri + 1) * 26 + ci) (cellView st ⟨ci, ri + 1⟩))

/-! ## Horizontal scrollbar (demo-local)

`Compose/Material/Scrollbar.lean` ships only `VerticalScrollbar`; this is
its horizontal transposition on a diet (no hover widening or auto-hide —
the thumb shows whenever the content overflows). **M14 promotion
candidate**: fold both axes into one Material scrollbar. -/

/-- The horizontal scrollbar's pointer coroutine: thumb press drags 1:1
through the travel↔scroll ratio; track press pages one viewport toward the
click (the `scrollbarGesture` logic with the axes swapped). -/
private partial def hScrollbarGesture (state : ScrollState)
    (minThumbPx : Float32) (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    let track := (← scope.size).width.toFloat32
    let viewport ← state.viewportSizeState.cell.get
    let content ← state.contentSizeState.cell.get
    let maxVal ← state.maxValueState.cell.get
    let v0 ← state.valueState.cell.get
    let (len, off) := scrollbarThumb track viewport content v0 minThumbPx
    if off ≤ ev.position.x && ev.position.x < off + len then
      let travel := track - len
      drag ev.position.x v0 (if travel ≤ 0 then 0 else maxVal / travel)
    else
      let _ ← state.scrollBy (if ev.position.x < off then -viewport else viewport)
  hScrollbarGesture state minThumbPx scope
where
  /-- Follow one thumb drag until release/window-leave. -/
  drag (x0 v0 ratio : Float32) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      ev.consume
      state.scrollTo (v0 + (ev.position.x - x0) * ratio)
      drag x0 v0 ratio
    | .release => ev.consume
    | .exit => pure ()
    | _ => drag x0 v0 ratio

/-- A minimal horizontal scrollbar for `state`'s scroll container: overlay
it along the content's bottom edge (e.g. `bs.align .bottomCenter
|>.fillMaxWidth`); it is 8 dp tall. See the section docstring for the diet
relative to `VerticalScrollbar`. -/
composable def HorizontalScrollbar (state : ScrollState)
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let density ← LocalDensity.current
  let value ← state.value
  let viewport ← state.viewportSize
  let content ← state.contentSize
  let minThumbPx := density.dpToPx scrollbarMinThumb
  let m := modifier
    |>.height 8
    |>.pointerInput (mixKeys (stringKey "Demos.Cells.HorizontalScrollbar") state.id)
        (hScrollbarGesture state minThumbPx)
    |>.drawBehind do
      let sz ← DrawScope.size
      if content > viewport then
        let (len, off) := scrollbarThumb sz.width viewport content value minThumbPx
        let hpx := density.dpToPx 6
        DrawScope.drawRoundRect (.solid (colors.onSurface.withAlpha 0.4))
          (RoundRect.circular ⟨off, sz.height - hpx, off + len, sz.height⟩ (hpx / 2))
  Layout m .leaf (policyInputs := some 0x68626172)

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
  Row (Modifier.fillMaxWidth |>.background colors.surfaceVariant
        |>.padding (horizontal := some 8) (vertical := some 5))
    (horizontalArrangement := .spacedBy 8)
    (verticalAlignment := .centerVertically)
    (content := fun _ => do
      Text (toString sel) (modifier := Modifier.testTag "formula-ref" |>.width 32)
        (style := { fontSize := 12 }) (color := some colors.primary)
      Text src (modifier := Modifier.testTag "formula-src")
        (style := { fontSize := 12 }))

/-- The assembled screen: formula bar on top; below it the pinned corner +
column headers, the pinned row headers, and the scrolling cell grid with
both scrollbars overlaid. -/
composable def cellsScreen (st : CellsState) (hs vs : ScrollState) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Column (Modifier.fillMaxSize |>.background colors.background)
    (content := fun cs => do
      formulaBar st
      Row (cs.weight 1 |>.fillMaxWidth) (content := fun rs => do
        Column (Modifier.width headerW) (content := fun lcs => do
          Box (Modifier.size headerW headerH |>.testTag "corner"
                |>.background colors.surfaceVariant
                |>.drawBehind (gridLineDraw colors.outlineVariant))
          rowHeaders st vs (lcs.weight 1 |>.fillMaxWidth))
        Column (rs.weight 1 |>.fillMaxHeight) (content := fun gcs => do
          columnHeaders st hs
          Box (gcs.weight 1 |>.fillMaxWidth) (content := fun bs => do
            gridCells st hs vs
            VerticalScrollbar vs (bs.align .centerEnd |>.fillMaxHeight)
            HorizontalScrollbar hs (bs.align .bottomCenter |>.fillMaxWidth)))))

/-- The Cells demo UI (see the module docstring). `initial` seeds the sheet
(tests boot it empty). -/
composable def cellsUi (initial : Sheet := seedSheet) : Composable Unit := do
  let st ← remember (CellsState.create initial)
  let hs ← rememberScrollState
  let vs ← rememberScrollState
  MaterialTheme (content := cellsScreen st hs vs)

end Demos.Cells
