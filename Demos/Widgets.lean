import Compose

/-!
# Widget gallery (`lake exe demo-widgets`)

The M9 showcase: every Material widget on one screen, fully wired to state —
buttons count their clicks, the checkbox/radios/switch toggle, the slider
drives the determinate progress indicators, and a dark-theme strip (a nested
`MaterialTheme .dark` around a `Surface`) shows the same widgets on the dark
baseline palette. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-widgets`.
-/

namespace Demos.Widgets
open Compose

/-- Buttons row + click tally. -/
composable def buttonsSection (clicks : MutableState Nat) : Composable Unit := do
  let n ← clicks.get
  Row {} (horizontalArrangement := .spacedBy 8) (verticalAlignment := .centerVertically)
    (content := fun _ => do
      Button (clicks.modify (· + 1)) (content := Text "Filled")
      OutlinedButton (clicks.modify (· + 1)) (content := Text "Outlined")
      TextButton (clicks.modify (· + 1)) (content := Text "Text")
      Button (pure ()) (enabled := false) (content := Text "Off"))
  Text s!"clicks: {n}"

/-- Checkbox, radio pair, and switch, each labeled. -/
composable def togglesSection (checked : MutableState Bool)
    (choice : MutableState Nat) (on : MutableState Bool) : Composable Unit := do
  let c ← checked.get
  let sel ← choice.get
  let o ← on.get
  Row {} (horizontalArrangement := .spacedBy 4) (verticalAlignment := .centerVertically)
    (content := fun _ => do
      Checkbox c checked.set
      Text (if c then "checked" else "unchecked")
      Spacer (Modifier.width 12)
      RadioButton (sel == 0) (choice.set 0)
      Text "A"
      RadioButton (sel == 1) (choice.set 1)
      Text "B"
      Spacer (Modifier.width 12)
      Switch o on.set
      Text (if o then "on" else "off"))

/-- Slider + the progress indicators it drives, plus the indeterminate pair. -/
composable def progressSection (amount : MutableState Float32) : Composable Unit := do
  let v ← amount.get
  Text s!"value: {(v * 100).toUInt32}%"
  Slider v amount.set (steps := 9)
  LinearProgressIndicator (some v)
  Row {} (horizontalArrangement := .spacedBy 16) (verticalAlignment := .centerVertically)
    (content := fun _ => do
      CircularProgressIndicator (some v)
      LinearProgressIndicator (modifier := Modifier.sizeIn (maxWidth := some 160))
      CircularProgressIndicator)

/-- The dark-theme strip: the same controls on the dark baseline palette. -/
composable def darkSection (checked : MutableState Bool)
    (on : MutableState Bool) : Composable Unit := do
  let c ← checked.get
  let o ← on.get
  MaterialTheme (colors := .dark) (content :=
    Surface (Modifier.fillMaxWidth) (shape := .rounded 12) (content := do
      Row (Modifier.padding (all := 12)) (horizontalArrangement := .spacedBy 8)
        (verticalAlignment := .centerVertically) (content := fun _ => do
          Text "Dark"
          Button (pure ()) (content := Text "Filled")
          Checkbox c checked.set
          Switch o on.set)))

/-- The gallery screen (see the module docstring). -/
composable def widgetsUi : Composable Unit := do
  let clicks ← remember (mutableStateOf (0 : Nat))
  let checked ← remember (mutableStateOf true)
  let choice ← remember (mutableStateOf (0 : Nat))
  let on ← remember (mutableStateOf false)
  let amount ← remember (mutableStateOf (0.5 : Float32))
  MaterialTheme (content :=
    Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 10)
      (content := fun _ => do
        Text "Material widgets" (style := { fontSize := 22 })
        buttonsSection clicks
        HorizontalDivider
        togglesSection checked choice on
        HorizontalDivider
        progressSection amount
        HorizontalDivider
        darkSection checked on))

end Demos.Widgets

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose widgets" 480 560 Demos.Widgets.widgetsUi
    { clearColor := Compose.ColorScheme.light.surface }
