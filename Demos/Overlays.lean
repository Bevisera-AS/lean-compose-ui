import Compose

/-!
# Overlay gallery (`lake exe demo-overlays`)

The M10 showcase: a 100-item `LazyColumn` with a desktop `VerticalScrollbar`
(wheel, thumb drag, track paging, auto-hide), an `ExposedDropdownMenuBox`
combobox opening a `DropdownMenu` (keyboard: Down/Up/Enter), and a button
opening an `AlertDialog` (scrim + Esc dismiss). Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-overlays`.
-/

namespace Demos.Overlays
open Compose

/-- The scrollable list + scrollbar strip. -/
composable def listSection (scroll : ScrollState) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Box (Modifier.fillMaxWidth |>.height 240
        |>.border 1 colors.outlineVariant
        |>.background colors.surface) (content := fun bs => do
    LazyColumn scroll (itemHeight := 28) (count := 100)
      (modifier := Modifier.fillMaxWidth)
      (itemContent := fun i =>
        Row (Modifier.padding (horizontal := some 12) (vertical := some 4)) (content := fun _ =>
          Text s!"Item {i}"))
    VerticalScrollbar scroll (bs.align .topEnd |>.fillMaxHeight))

/-- The flavor combobox: `ExposedDropdownMenuBox` + `DropdownMenu`. -/
composable def flavorPicker (choice : MutableState String)
    (expanded : MutableState Bool) : Composable Unit := do
  let flavors := ["Vanilla", "Chocolate", "Pistachio", "Stracciatella"]
  let sel ← choice.get
  let open' ← expanded.get
  ExposedDropdownMenuBox open' expanded.set (content := fun scope => do
    ExposedDropdownMenuField scope sel (expanded := open')
    let anchor ← scope.anchor
    DropdownMenu open' (onDismissRequest := expanded.set false) (anchor := anchor)
      (content := do
        for f in flavors do
          keyed f (DropdownMenuItem f (onClick := do choice.set f; expanded.set false))))

/-- The dialog trigger + the dialog itself. -/
composable def dialogSection (dialogOpen : MutableState Bool) : Composable Unit := do
  let open' ← dialogOpen.get
  Button (dialogOpen.set true) (content := Text "Open dialog")
  if open' then
    AlertDialog (onDismissRequest := dialogOpen.set false)
      (title := "Discard draft?")
      (text := "The draft and its 100 lazily composed items will be lost.")
      (confirmButton := TextButton (dialogOpen.set false) (content := Text "Discard"))
      (dismissButton := some (TextButton (dialogOpen.set false) (content := Text "Keep")))

/-- The gallery screen (see the module docstring). -/
composable def overlaysUi : Composable Unit := do
  let scroll ← rememberScrollState
  let choice ← remember (mutableStateOf "Vanilla")
  let menuOpen ← remember (mutableStateOf false)
  let dialogOpen ← remember (mutableStateOf false)
  MaterialTheme (content :=
    Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12)
      (content := fun _ => do
        Text "Scroll, menus, dialogs" (style := { fontSize := 22 })
        listSection scroll
        Row {} (horizontalArrangement := .spacedBy 12)
          (verticalAlignment := .centerVertically) (content := fun _ => do
            flavorPicker choice menuOpen
            dialogSection dialogOpen)))

end Demos.Overlays

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose overlays" 480 420 Demos.Overlays.overlaysUi
    { clearColor := Compose.ColorScheme.light.background }
