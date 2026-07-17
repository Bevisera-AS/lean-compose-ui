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
  Box (modifier := Modifier.fillMaxWidth |>.height 240
        |>.border 1 colors.outlineVariant
        |>.background colors.surface) do
    LazyColumn scroll (itemHeight := 28) (count := 100)
      (modifier := Modifier.fillMaxWidth)
      fun i =>
        Row (modifier := Modifier.padding (horizontal := some 12) (vertical := some 4)) do
          Text s!"Item {i}"
    VerticalScrollbar scroll (Modifier.align .topEnd |>.fillMaxHeight)

/-- The flavor combobox: `ExposedDropdownMenuBox` + `DropdownMenu`. -/
composable def flavorPicker (choice : MutableState String)
    (expanded : MutableState Bool) : Composable Unit := do
  let flavors := ["Vanilla", "Chocolate", "Pistachio", "Stracciatella"]
  let sel ← choice.get
  let open' ← expanded.get
  ExposedDropdownMenuBox open' expanded.set fun scope => do
    ExposedDropdownMenuField scope sel (expanded := open')
    let anchor ← scope.anchor
    DropdownMenu open' (onDismissRequest := expanded.set false) (anchor := anchor)
        (matchAnchorWidth := true) do
      for f in flavors do
        keyed f (DropdownMenuItem f (onClick := do choice.set f; expanded.set false))

/-- The dialog trigger + the dialog itself. -/
composable def dialogSection (dialogOpen : MutableState Bool) : Composable Unit := do
  let open' ← dialogOpen.get
  Button (dialogOpen.set true) (Text "Open dialog")
  if open' then
    AlertDialog (onDismissRequest := dialogOpen.set false)
      (title := "Discard draft?")
      (text := "The draft and its 100 lazily composed items will be lost.")
      (confirmButton := TextButton (dialogOpen.set false) (Text "Discard"))
      (dismissButton := some (TextButton (dialogOpen.set false) (Text "Keep")))

/-- The frosted dialog: `blurBehind` Gaussian-blurs the app content behind
the scrim while open (GPU backend; the software renderer keeps the plain
scrim). -/
composable def frostedSection (frostedOpen : MutableState Bool) : Composable Unit := do
  let open' ← frostedOpen.get
  Button (frostedOpen.set true) (Text "Frosted dialog")
  if open' then
    AlertDialog (onDismissRequest := frostedOpen.set false)
      (title := "Frosted glass")
      (text := "The content behind this dialog is Gaussian-blurred (16 dp).")
      (confirmButton := TextButton (frostedOpen.set false) (Text "Close"))
      (blurBehind := 16)

/-- The gallery screen (see the module docstring). -/
composable def overlaysUi : Composable Unit := do
  let scroll ← rememberScrollState
  let choice ← remember (mutableStateOf "Vanilla")
  let menuOpen ← remember (mutableStateOf false)
  let dialogOpen ← remember (mutableStateOf false)
  let frostedOpen ← remember (mutableStateOf false)
  MaterialTheme do
    Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12) do
      Text "Scroll, menus, dialogs" (style := { fontSize := 22 })
      listSection scroll
      Row (horizontalArrangement := .spacedBy 12)
          (verticalAlignment := .centerVertically) do
        flavorPicker choice menuOpen
        dialogSection dialogOpen
        frostedSection frostedOpen

end Demos.Overlays

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose overlays" 480 420 Demos.Overlays.overlaysUi
    { clearColor := Compose.ColorScheme.light.background }
