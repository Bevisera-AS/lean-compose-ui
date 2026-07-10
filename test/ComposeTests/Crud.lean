import Compose
import ComposeTests.Harness
import Demos.Crud

/-!
# CRUD demo behavior tests (`test/ComposeTests/Crud.lean`)

The 7GUIs *CRUD* demo (`Demos/Crud.lean`) driven through the MT framework:
create/update/delete via the real buttons, selection via real row clicks,
prefix filtering via real typing. Selection is by entry id, so we prove it
survives a filter that hides the selected row. We inject the demo's state into
`crudBody` and read the model back directly, alongside semantics assertions.
(The pure list model is covered by `#guard`s in `Demos/Crud.lean`.)
-/

namespace Tests.Crud
open Compose Compose.Test Tests.Harness Demos.Crud

/-- Fresh, seeded demo state for one scenario. -/
private def freshState : IO (MutableState Db × MutableState String ×
    MutableState String × MutableState String) := do
  return (← mutableStateOf seed, ← mutableStateOf "", ← mutableStateOf "",
          ← mutableStateOf "")

/-- Create appends an entry from the field contents; row clicks select the
underlying entry (by id). -/
private def createSelect : IO Unit := do
  let (db, filter, nm, sn) ← freshState
  runComposeTest (crudBody db filter nm sn) (width := 540) (height := 460) do
    assertExists (.text "Emil, Hans")
    assertExists (.text "Mustermann, Max")
    assertExists (.text "Tisch, Roman")
    -- Create a new entry from the two fields.
    typeText (.tag "name") "Ada"
    typeText (.tag "surname") "Lovelace"
    click (.tag "create")
    assertExists (.text "Lovelace, Ada")
    checkEq "db grew to 4" (← db.get).entries.size 4
    -- Click a row → it publishes `selected`, and the model records its id.
    click (.tag "row-0")
    assertSelected (.tag "row-0")
    checkEq "selected id 0" (← db.get).selected (some 0)
    -- Selecting another row moves the selection.
    click (.tag "row-2")
    assertSelected (.tag "row-2")
    assertSelected (.tag "row-0") (expected := false)
    checkEq "selected id 2" (← db.get).selected (some 2)

/-- Update rewrites the selected entry in place; Delete removes it and clears
the selection. -/
private def updateDelete : IO Unit := do
  let (db, filter, nm, sn) ← freshState
  runComposeTest (crudBody db filter nm sn) (width := 540) (height := 460) do
    click (.tag "row-2")                     -- select "Tisch, Roman"
    typeText (.tag "name") "Romana"
    typeText (.tag "surname") "Tischler"
    click (.tag "update")
    assertExists (.text "Tischler, Romana")
    assertMissing (.text "Tisch, Roman")
    checkEq "update keeps the count" (← db.get).entries.size 3
    -- Delete the selected entry.
    click (.tag "delete")
    assertMissing (.text "Tischler, Romana")
    checkEq "delete drops the count" (← db.get).entries.size 2
    checkEq "delete clears the selection" (← db.get).selected none

/-- Filtering narrows the visible list without changing which entry is
selected: the selection is by id, so it survives even when its row is hidden. -/
private def filterSelectionSurvival : IO Unit := do
  let (db, filter, nm, sn) ← freshState
  runComposeTest (crudBody db filter nm sn) (width := 540) (height := 460) do
    click (.tag "row-0")                     -- select "Emil, Hans"
    checkEq "selected id 0" (← db.get).selected (some 0)
    -- Narrow by surname prefix so the selected row is hidden.
    typeText (.tag "filter") "T"
    assertMissing (.text "Emil, Hans")
    assertExists (.text "Tisch, Roman")
    checkEq "selection survives the filter" (← db.get).selected (some 0)
    -- Clearing the filter brings the row back, still selected.
    filter.set ""
    assertExists (.text "Emil, Hans")
    assertSelected (.tag "row-0")

/-- Update/Delete are disabled with no selection, enabled once a row is
selected, and disabled again after Delete clears it. -/
private def disabledButtons : IO Unit := do
  let (db, filter, nm, sn) ← freshState
  runComposeTest (crudBody db filter nm sn) (width := 540) (height := 460) do
    assertDisabled (.tag "update")
    assertDisabled (.tag "delete")
    assertEnabled (.tag "create")            -- Create never needs a selection
    click (.tag "row-1")
    assertEnabled (.tag "update")
    assertEnabled (.tag "delete")
    click (.tag "delete")
    assertDisabled (.tag "update")
    assertDisabled (.tag "delete")

/-- The CRUD group. -/
def run : IO Unit := do
  scenario "createSelect" createSelect
  scenario "updateDelete" updateDelete
  scenario "filterSelectionSurvival" filterSelectionSurvival
  scenario "disabledButtons" disabledButtons

end Tests.Crud
