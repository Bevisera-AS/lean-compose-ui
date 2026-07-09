import Compose
import ComposeTests.Harness
import Demos.Cells.Ui

/-!
# CellsUi group (`test/ComposeTests/CellsUi.lean`)

MT behavior suite for the M13b Cells demo (`Demos/Cells/Ui.lean`), driving
the real UI through the framework's input pipeline: selection by click and
arrow keys, editing (double-click / Enter / type-to-edit) with commit,
cancel, and click-away semantics, dependent-cell propagation through the
engine, cycle display and recovery, and 2-axis virtualization with sticky
headers (far cells compose, near cells leave, headers pin correctly).
-/

namespace Tests.CellsUi
open Compose Compose.Test Tests.Harness Demos.Cells

/-- Boot the Cells screen on an empty sheet in a window large enough for a
several-column × a-dozen-row viewport. -/
private def cellsTest (body : TestM Unit) : IO Unit :=
  runComposeTest (content := cellsUi (initial := Sheet.empty)) body
    (width := 480) (height := 360)

/-- Commit `input` into the cell tagged `cell-{ref}` through the real edit
flow: double-click opens the editor, ctrl-A replaces any seeded source,
Enter commits. -/
private def setCell (ref input : String) : TestM Unit := do
  doubleClick (.tag s!"cell-{ref}")
  typeText (.tag "cell-editor") ""            -- click-focus the editor
  pressKey .a (mods := Sdl.Keymod.lCtrl)      -- select the seeded source …
  typeText (.tag "cell-editor") input         -- … and replace it
  pressKey .«return»

/-! ## Selection: click, arrows, formula bar -/

private def selectionFlow : IO Unit := cellsTest do
  assertSelected (.tag "cell-A1")             -- A1 selected at boot
  click (.tag "cell-B2")
  assertSelected (.tag "cell-B2")
  assertSelected (.tag "cell-A1") (expected := false)
  assertTextEquals (.tag "formula-ref") "B2"  -- formula bar follows
  -- Arrow keys move the selection (the click focused the grid).
  pressKey .down
  assertSelected (.tag "cell-B3")
  pressKey .right
  assertSelected (.tag "cell-C3")
  pressKey .up
  pressKey .left
  assertSelected (.tag "cell-B2")
  -- Clamped at the sheet edges.
  click (.tag "cell-A1")
  pressKey .left
  pressKey .up
  assertSelected (.tag "cell-A1")

/-! ## Editing: open, commit, click-away, formula bar draft -/

private def editFlow : IO Unit := cellsTest do
  assertMissing (.tag "cell-editor")
  doubleClick (.tag "cell-B2")
  assertExists (.tag "cell-editor")
  typeText (.tag "cell-editor") "42"
  assertTextEquals (.tag "formula-src") "42"  -- formula bar shows the draft
  pressKey .«return»                          -- Enter bubbles out and commits
  assertMissing (.tag "cell-editor")
  assertTextEquals (.tag "cell-B2") "42"
  assertTextEquals (.tag "formula-src") "42"  -- now the committed source
  -- Re-opening seeds the editor with the source, and clicking another cell
  -- commits (spreadsheet click-away).
  doubleClick (.tag "cell-C1")
  typeText (.tag "cell-editor") "7"
  click (.tag "cell-A3")
  assertMissing (.tag "cell-editor")
  assertTextEquals (.tag "cell-C1") "7"
  assertSelected (.tag "cell-A3")

/-! ## Type-to-edit and grid-focused editing (no editor click needed) -/

private def typeToEdit : IO Unit := cellsTest do
  click (.tag "cell-E5")                      -- selects; grid holds focus
  textInput "31"                              -- typing starts a replacing edit
  awaitIdle
  assertExists (.tag "cell-editor")
  assertTextEquals (.tag "cell-editor") "31"
  pressKey .backspace                         -- grid-focused draft trimming
  pressKey .«return»
  assertMissing (.tag "cell-editor")
  assertTextEquals (.tag "cell-E5") "3"
  -- Enter re-opens the editor on the selection, seeded with the source.
  pressKey .«return»
  assertExists (.tag "cell-editor")
  assertTextEquals (.tag "cell-editor") "3"
  pressKey .escape
  -- Delete clears the selected cell without an editor.
  pressKey .delete
  assertTextEquals (.tag "cell-E5") ""

/-! ## Esc cancels without committing -/

private def escCancels : IO Unit := cellsTest do
  setCell "C3" "5"
  doubleClick (.tag "cell-C3")
  typeText (.tag "cell-editor") "99"          -- draft now "599"
  pressKey .escape                            -- bubbles out of the field
  assertMissing (.tag "cell-editor")
  assertTextEquals (.tag "cell-C3") "5"       -- unchanged
  assertTextEquals (.tag "formula-src") "5"

/-! ## Formulas: dependent cells recompute on commit -/

private def formulaPropagation : IO Unit := cellsTest do
  setCell "A1" "2"
  setCell "B1" "=A1*3"
  assertTextEquals (.tag "cell-B1") "6"
  setCell "C1" "=SUM(A1:B1)"
  assertTextEquals (.tag "cell-C1") "8"
  -- Changing A1 flows through both dependents.
  setCell "A1" "5"
  assertTextEquals (.tag "cell-B1") "15"
  assertTextEquals (.tag "cell-C1") "20"
  -- The formula bar shows the *source* of a formula cell, not its value.
  click (.tag "cell-B1")
  assertTextEquals (.tag "formula-src") "=A1*3"
  assertTextEquals (.tag "cell-B1") "15"

/-! ## Errors and cycles display distinctly and recover -/

private def cycleFlow : IO Unit := cellsTest do
  setCell "D1" "=D1+1"                        -- self-reference
  assertTextEquals (.tag "cell-D1") "#CYCLE!"
  setCell "D2" "=D1*2"                        -- errors propagate
  assertTextEquals (.tag "cell-D2") "#CYCLE!"
  setCell "D1" "7"                            -- breaking the cycle recovers
  assertTextEquals (.tag "cell-D1") "7"
  assertTextEquals (.tag "cell-D2") "14"
  setCell "D3" "=1/0"
  assertTextEquals (.tag "cell-D3") "#DIV/0!"

/-! ## 2-axis virtualization and sticky headers -/

private def virtualizationFlow : IO Unit := cellsTest do
  -- Boot: the top-left window is composed, the far sheet is not.
  assertExists (.tag "cell-A1")
  assertMissing (.tag "cell-A40")
  assertExists (.tag "colh-A")
  assertExists (.tag "rowh-1")
  assertMissing (.tag "rowh-40")
  assertExists (.tag "corner")
  -- 22 wheel notches ≈ 1100 px ≈ 39 rows down.
  scrollBy (.tag "grid") ⟨0, -22⟩
  assertExists (.tag "cell-A40")              -- far cell now composed
  assertMissing (.tag "cell-A1")              -- near cell left the window
  assertExists (.tag "colh-A")                -- column headers stay pinned
  assertMissing (.tag "rowh-1")               -- row headers scrolled along
  assertExists (.tag "rowh-40")
  assertExists (.tag "corner")                -- corner pinned both ways
  -- 13 notches right ≈ 650 px ≈ 8 columns (positive wheel x = right).
  scrollBy (.tag "grid") ⟨13, 0⟩
  assertExists (.tag "cell-M40")              -- both axes virtualized
  assertMissing (.tag "cell-A40")
  assertExists (.tag "colh-M")                -- column headers followed
  assertMissing (.tag "colh-A")
  assertExists (.tag "rowh-40")               -- row headers stay pinned
  assertExists (.tag "corner")
  -- Scrolling back restores the origin window.
  scrollBy (.tag "grid") ⟨0, 22⟩
  scrollBy (.tag "grid") ⟨-13, 0⟩
  assertExists (.tag "cell-A1")
  assertMissing (.tag "cell-M40")

/-! ## Diagonal wheel events split per axis (M14b) -/

private def diagonalWheel : IO Unit := cellsTest do
  -- One diagonal wheel event: 13 notches right and 22 down at once. The
  -- horizontal container consumes x, the vertical one y — both axes move.
  scrollBy (.tag "grid") ⟨13, -22⟩
  assertExists (.tag "cell-M40")
  assertMissing (.tag "cell-A1")
  assertExists (.tag "colh-M")                -- headers followed both axes
  assertExists (.tag "rowh-40")
  -- And diagonally back to the origin.
  scrollBy (.tag "grid") ⟨-13, 22⟩
  assertExists (.tag "cell-A1")
  assertMissing (.tag "cell-M40")

/-! ## Horizontal scrollbar (the Material `HorizontalScrollbar`) -/

private def hScrollbarDrag : IO Unit := cellsTest do
  assertExists (.tag "hscrollbar")
  -- The thumb sits at the track start at boot (scroll value 0): press inside
  -- it and drag right — the grid follows through the travel↔scroll ratio
  -- (~4.7 content px per track px here), far columns compose, near ones go.
  let b ← boundsOf (.tag "hscrollbar")
  let start : Offset := ⟨b.left + 20, (b.top + b.bottom) / 2⟩
  mouseDown start
  for i in [1:5] do
    mouseMove (start + (⟨30 * i.toFloat32, 0⟩ : Offset))
  mouseUp (start + (⟨120, 0⟩ : Offset))
  awaitIdle
  assertMissing (.tag "cell-A1")              -- scrolled off to the left
  assertMissing (.tag "colh-A")               -- headers follow the same state
  assertExists (.tag "cell-H1")               -- a mid-sheet column composed
  assertExists (.tag "rowh-1")                -- the vertical axis untouched

/-- The CellsUi group. -/
def run : IO Unit := do
  scenario "selectionFlow" selectionFlow
  scenario "editFlow" editFlow
  scenario "typeToEdit" typeToEdit
  scenario "escCancels" escCancels
  scenario "formulaPropagation" formulaPropagation
  scenario "cycleFlow" cycleFlow
  scenario "virtualizationFlow" virtualizationFlow
  scenario "diagonalWheel" diagonalWheel
  scenario "hScrollbarDrag" hScrollbarDrag

end Tests.CellsUi
