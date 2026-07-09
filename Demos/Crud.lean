import Compose

/-!
# CRUD demo (`lake exe demo-crud`)

The 7GUIs *CRUD* task (https://eugenkiss.github.io/7guis/tasks): a filter
prefix field, a listbox of names shown "Surname, Name" and filtered by
**surname** prefix, Name/Surname text fields, and Create/Update/Delete
buttons. Update/Delete act on the selected entry and are disabled with no
selection; Create appends a new entry from the field contents.

The list model is a set of pure functions (`Db.*`, `#guard`ed inline);
selection is by stable **entry id**, not visual row index, so filtering the
list never changes *which* entry is selected. UI behavior is proven in
`test/ComposeTests/Crud.lean`. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-crud`.
-/

namespace Demos.Crud
open Compose

/-! ## Pure list model -/

/-- A person entry. `display` renders it as the "Surname, Name" listbox line. -/
structure Entry where
  /-- Given name. -/
  name : String
  /-- Family name; the field the filter matches on. -/
  surname : String
  deriving BEq, Repr, Inhabited

/-- The listbox line for an entry: "Surname, Name". -/
def Entry.display (e : Entry) : String := s!"{e.surname}, {e.name}"

#guard ({ name := "Hans", surname := "Emil" } : Entry).display == "Emil, Hans"

/-- The CRUD database: id-tagged entries, the next fresh id, and the selected
entry's id (if any). Selection is by id so it is stable across filtering,
creation, and deletion of *other* rows. -/
structure Db where
  /-- `(id, entry)` in insertion order. -/
  entries : Array (Nat × Entry)
  /-- The id the next `create` will assign (monotonic). -/
  nextId : Nat
  /-- The selected entry's id, or `none`. -/
  selected : Option Nat
  deriving BEq, Inhabited

/-- The empty database. -/
def Db.empty : Db := { entries := #[], nextId := 0, selected := none }

/-- Append a fresh entry (assigned the next id); selection is unchanged.
Mirrors the task's "Create". -/
def Db.create (db : Db) (name surname : String) : Db :=
  { db with
    entries := db.entries.push (db.nextId, { name, surname })
    nextId := db.nextId + 1 }

/-- Select the entry with `id`. -/
def Db.select (db : Db) (id : Nat) : Db := { db with selected := some id }

/-- The selected entry, if any. -/
def Db.selectedEntry (db : Db) : Option Entry :=
  db.selected.bind fun id => (db.entries.find? (·.1 == id)).map (·.2)

/-- Overwrite the selected entry's name/surname; a no-op with no selection.
Mirrors the task's "Update". -/
def Db.update (db : Db) (name surname : String) : Db :=
  match db.selected with
  | none => db
  | some id =>
    { db with entries := db.entries.map fun (i, e) =>
        if i == id then (i, { name, surname }) else (i, e) }

/-- Delete the selected entry and clear the selection; a no-op with no
selection. Mirrors the task's "Delete". -/
def Db.delete (db : Db) : Db :=
  match db.selected with
  | none => db
  | some id => { db with entries := db.entries.filter (·.1 != id), selected := none }

/-- Whether `surname` starts with `pfx` (case-insensitive). -/
def matchesPrefix (pfx surname : String) : Bool :=
  surname.toLower.startsWith pfx.toLower

/-- The entries whose surname starts with `pfx` (a pure view — leaves the
database, and the selection, untouched). Mirrors the filtered listbox. -/
def Db.filtered (db : Db) (pfx : String) : Array (Nat × Entry) :=
  db.entries.filter fun (_, e) => matchesPrefix pfx e.surname

/-- The seed data from the task: Emil / Mustermann / Tisch (ids 0/1/2). -/
def seed : Db :=
  Db.empty
    |>.create "Hans" "Emil"
    |>.create "Max" "Mustermann"
    |>.create "Roman" "Tisch"

-- Seeding and ids.
#guard seed.entries.size == 3
#guard seed.nextId == 3
#guard seed.selected == none
-- Filtering by surname prefix, case-insensitively.
#guard (seed.filtered "").size == 3
#guard (seed.filtered "M").map (·.2.display) == #["Mustermann, Max"]
#guard (seed.filtered "m").map (·.2.surname) == #["Mustermann"]
#guard (seed.filtered "T").map (·.2.display) == #["Tisch, Roman"]
#guard (seed.filtered "Z").isEmpty
-- Create appends and bumps the id.
#guard (seed.create "Ada" "Lovelace").entries.size == 4
#guard (seed.create "Ada" "Lovelace").nextId == 4
#guard ((seed.create "Ada" "Lovelace").filtered "L").map (·.2.display) == #["Lovelace, Ada"]
-- Select / selectedEntry.
#guard ((seed.select 1).selectedEntry).map Entry.surname == some "Mustermann"
#guard (seed.select 9).selectedEntry == none   -- unknown id resolves to nothing
-- Update touches only the selected entry.
#guard ((seed.select 0).update "Hansi" "Emilio").selectedEntry
        == some { name := "Hansi", surname := "Emilio" }
#guard (((seed.select 0).update "X" "Y").entries[1]!).2
        == { name := "Max", surname := "Mustermann" }
#guard seed.update "X" "Y" == seed          -- no selection → no-op
-- Delete removes the selected entry and clears selection.
#guard ((seed.select 1).delete).entries.size == 2
#guard ((seed.select 1).delete).selected == none
#guard (((seed.select 1).delete).filtered "M").isEmpty
#guard seed.delete == seed                  -- no selection → no-op
-- Selection is by id, so narrowing the filter never changes it.
#guard !((seed.select 0).filtered "T").any (·.1 == 0)   -- Emil (id 0) hidden by "T" …
#guard ((seed.select 0).selected) == some 0             -- … yet id 0 stays selected.

/-! ## UI -/

/-- One selectable listbox row: clickable, highlighted when selected, and
publishing its `selected` semantics so the MT suite can assert on it. -/
composable def nameRow (id : Nat) (e : Entry) (selected : Bool)
    (onSelect : IO Unit) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Box (Modifier.testTag s!"row-{id}"
        |>.semantics (selected := some selected)
        |>.clickable onSelect
        |>.fillMaxWidth
        |>.background (if selected then colors.primaryContainer else colors.surface)
        |>.padding (horizontal := some 8) (vertical := some 4))
    (content := Text e.display)

/-- The CRUD screen, factored on injected state so the MT suite can drive and
inspect it directly. -/
composable def crudBody (db : MutableState Db)
    (filter «name» surname : MutableState String) : Composable Unit := do
  let d ← db.get
  let f ← filter.get
  let visible := d.filtered f
  let sel := d.selected
  Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12)
    (content := do
      Text "CRUD" (style := { fontSize := 22 })
      TextFieldS f filter.set (modifier := Modifier.testTag "filter")
        (label := some "Filter prefix")
      Row {} (horizontalArrangement := .spacedBy 16) (content := do
        Column (Modifier.testTag "list" |>.width 220) (content :=
          for (id, e) in visible do
            keyed (toString id) (nameRow id e (sel == some id) (db.modify (·.select id))))
        Column {} (verticalArrangement := .spacedBy 8) (content := do
          TextFieldS (← «name».get) «name».set (modifier := Modifier.testTag "name")
            (label := some "Name")
          TextFieldS (← surname.get) surname.set (modifier := Modifier.testTag "surname")
            (label := some "Surname")))
      Row {} (horizontalArrangement := .spacedBy 8) (content := do
        Button (do db.modify (·.create (← «name».get) (← surname.get)))
          (modifier := Modifier.testTag "create") (content := Text "Create")
        Button (do db.modify (·.update (← «name».get) (← surname.get)))
          (enabled := sel.isSome) (modifier := Modifier.testTag "update")
          (content := Text "Update")
        Button (db.modify (·.delete)) (enabled := sel.isSome)
          (modifier := Modifier.testTag "delete") (content := Text "Delete")))

/-- The CRUD demo screen (see the module docstring). -/
composable def crudUi : Composable Unit := do
  let db ← remember (mutableStateOf seed)
  let filter ← remember (mutableStateOf "")
  let «name» ← remember (mutableStateOf "")
  let surname ← remember (mutableStateOf "")
  MaterialTheme (content := crudBody db filter «name» surname)

end Demos.Crud
