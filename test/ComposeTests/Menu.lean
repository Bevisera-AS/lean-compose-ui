import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Menu width test group (`test/ComposeTests/Menu.lean`)

Regression scenarios for dropdown sizing (the "menu spans the full window"
bug): an open `DropdownMenu` wraps its widest item (112dp floor) instead of
stretching to the overlay's window-sized max constraints, and an
`ExposedDropdownMenuBox` menu (`matchAnchorWidth`) matches its field's width.
The MenuBar dropdown path is covered in the MenuBar group; item bounds come
from the merged semantics tree (a `DropdownMenuItem`'s clickable row absorbs
its label text, so `boundsOf (.text …)` is the full hover row).
-/

namespace Tests.Menu
open Compose Compose.Test Tests.Harness

/-- Plain dropdown with short items in the 480px-wide default test window. -/
private def dropdownUi (expanded : MutableState Bool) : Composable Unit :=
  Tests.restartable 1 do
    let isOpen ← expanded.get
    Column (modifier := Modifier.fillMaxSize) do
      Button (expanded.set true) (Text "Open")
      DropdownMenu isOpen (onDismissRequest := expanded.set false) do
        DropdownMenuItem "Cut" (onClick := expanded.set false)
        DropdownMenuItem "Copy" (onClick := expanded.set false)
        DropdownMenuItem "Select all" (onClick := expanded.set false)

/-- An open menu is as wide as its widest item (112dp floor), never the
window. -/
private def dropdownWrapsWidestItem : IO Unit := do
  let expanded ← MutableState.create false
  runComposeTest (dropdownUi expanded) do
    click (.text "Open")
    settle
    let b ← boundsOf (.text "Copy")
    check s!"dropdown: item row does not span the window (width {b.width})"
      (b.width < 320)
    check s!"dropdown: menu wraps its widest item (width {b.width})"
      (b.width ≥ 112 && b.width ≤ 200)
    -- Hover rows all share the menu's width.
    let w ← boundsOf (.text "Select all")
    checkEq "dropdown: rows share one width" w.width b.width

/-- An exposed-dropdown combobox: field + menu matching the field's width. -/
private def exposedUi (expanded : MutableState Bool) (sel : MutableState String) :
    Composable Unit :=
  Tests.restartable 1 do
    let isOpen ← expanded.get
    Box (modifier := Modifier.fillMaxSize |>.padding (all := 8)) do
      ExposedDropdownMenuBox isOpen expanded.set fun scope => do
        ExposedDropdownMenuField scope (← sel.get) (expanded := isOpen)
          (modifier := Modifier.testTag "field" |>.width 200)
        let anchor ← scope.anchor
        DropdownMenu isOpen (onDismissRequest := expanded.set false)
          (anchor := anchor) (matchAnchorWidth := true) do
          for name in ["Alpha", "Beta"] do
            keyed name <| DropdownMenuItem name
              (onClick := do sel.set name; expanded.set false)

/-- An exposed dropdown's menu matches the field's width — not the widest
item, not the window (Material's `ExposedDropdownMenuBox` convention). -/
private def exposedMatchesFieldWidth : IO Unit := do
  let expanded ← MutableState.create false
  let sel ← MutableState.create "Alpha"
  runComposeTest (exposedUi expanded sel) do
    click (.tag "field")
    settle
    let fb ← boundsOf (.tag "field")
    let ib ← boundsOf (.text "Beta")
    check s!"exposed: menu row matches the field width ({ib.width} vs {fb.width})"
      ((ib.width - fb.width).abs ≤ 1)
    check s!"exposed: row does not span the window (width {ib.width})"
      (ib.width < 320)

/-- The Menu group. -/
def run : IO Unit := do
  scenario "dropdownWrapsWidestItem" dropdownWrapsWidestItem
  scenario "exposedMatchesFieldWidth" exposedMatchesFieldWidth

end Tests.Menu
