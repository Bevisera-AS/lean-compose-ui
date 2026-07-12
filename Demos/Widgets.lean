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
  Row (horizontalArrangement := .spacedBy 8) (verticalAlignment := .centerVertically) do
    Button (clicks.modify (· + 1)) (Text "Filled")
    OutlinedButton (clicks.modify (· + 1)) (Text "Outlined")
    TextButton (clicks.modify (· + 1)) (Text "Text")
    Button (pure ()) (enabled := false) (Text "Off")
  Text s!"clicks: {n}"

/-- Checkbox, radio pair, and switch, each labeled. -/
composable def togglesSection (checked : MutableState Bool)
    (choice : MutableState Nat) (on : MutableState Bool) : Composable Unit := do
  let c ← checked.get
  let sel ← choice.get
  let o ← on.get
  Row (horizontalArrangement := .spacedBy 4) (verticalAlignment := .centerVertically) do
    Checkbox c checked.set
    Text (if c then "checked" else "unchecked")
    Spacer (Modifier.width 12)
    RadioButton (sel == 0) (choice.set 0)
    Text "A"
    RadioButton (sel == 1) (choice.set 1)
    Text "B"
    Spacer (Modifier.width 12)
    Switch o on.set
    Text (if o then "on" else "off")

/-- Slider + the progress indicators it drives, plus the indeterminate pair. -/
composable def progressSection (amount : MutableState Float32) : Composable Unit := do
  let v ← amount.get
  Text s!"value: {(v * 100).toUInt32}%"
  Slider v amount.set (steps := 9)
  LinearProgressIndicator (some v)
  Row (horizontalArrangement := .spacedBy 16) (verticalAlignment := .centerVertically) do
    CircularProgressIndicator (some v)
    LinearProgressIndicator (modifier := Modifier.sizeIn (maxWidth := some 160))
    CircularProgressIndicator

/-- Generated-bitmap strip (M-f): the `Image` composable over an `ofPixels`
checkerboard at different content scales and samplings — no binary assets. -/
composable def imagesSection : Composable Unit := do
  let img ← remember (Draw.ImageBitmap.ofPixels 8 8 fun x y =>
    if (x + y) % 2 == 0 then Color.hex 0xFF6200EE else .white)
  Row (horizontalArrangement := .spacedBy 12) (verticalAlignment := .centerVertically) do
    Image img (modifier := Modifier.size 48 48) (contentScale := .fillBounds)
      (sampling := .nearest) (desc := some "checkerboard nearest")
    Image img (modifier := Modifier.size 48 48) (contentScale := .fillBounds)
      (desc := some "checkerboard linear")
    Image img (modifier := Modifier.size 64 40) (contentScale := .crop)
      (sampling := .nearest) (desc := some "checkerboard crop")
    Image img (desc := some "checkerboard natural")

/-- Gradient brushes (M-h): radial and sweep fills — evaluated per fragment
on the GPU backend, per-vertex fallback on SDL. -/
composable def gradientsSection : Composable Unit := do
  Row (horizontalArrangement := .spacedBy 12) (verticalAlignment := .centerVertically) do
    Box (modifier := (Modifier.size 48 48).drawBehind do
      Draw.DrawScope.drawCircle
        (.radial (Color.hex 0xFFBB86FC) (Color.hex 0xFF6200EE) ⟨24, 24⟩ 24) ⟨24, 24⟩ 24)
    Box (modifier := (Modifier.size 48 48).drawBehind do
      Draw.DrawScope.drawCircle
        (.sweepGradient #[(0, Color.hex 0xFF03DAC6), (1, Color.hex 0xFF018786)] ⟨24, 24⟩)
        ⟨24, 24⟩ 24)
    Box (modifier := (Modifier.size 72 48).drawBehind do
      Draw.DrawScope.drawRect (.radial .white (Color.hex 0xFFB00020) ⟨36, 24⟩ 48)
        ⟨0, 0⟩ ⟨72, 48⟩)
    Text "radial · sweep"

/-- Layer transforms (M-g): a spinner on an infinite rotation, a static
rotate+squash, and a press-to-scale chip (press interactions drive an
animated `graphicsLayer` scale). -/
composable def transformsSection : Composable Unit := do
  let it ← rememberInfiniteTransition
  let angle ← it.animateFloat 0 360 (.infiniteRepeatable (.tween 1400 0 .linear))
  let source ← rememberInteractionSource
  let scale ← animateFloatAsState (if (← source.pressed.get) then 1.3 else 1.0)
    (.tween 120 0 .linear)
  Row (horizontalArrangement := .spacedBy 24) (verticalAlignment := .centerVertically) do
    Box (modifier := Modifier.graphicsLayer (rotationZ := (← angle.get))
          |>.size 28 28 |>.background (Color.hex 0xFF6200EE) (.rounded 6))
    Box (modifier := Modifier.graphicsLayer (rotationZ := 30) (scaleY := 0.8)
          |>.size 28 28 |>.background (Color.hex 0xFF03DAC6) (.rounded 6))
    Box (modifier := Modifier.graphicsLayer (scaleX := (← scale.get)) (scaleY := (← scale.get))
          |>.clickable (pure ()) (source := some source)
          |>.size 28 28 |>.background (Color.hex 0xFFB00020) (.rounded 14))
    Text "spin · tilt · press"

/-- Layer blur (M-i): the same two-circle motif sharp and under
`Modifier.blur` — Gaussian-blurred on the GPU backend; the SDL backend draws
it unblurred (the documented fallback). -/
composable def effectsSection : Composable Unit := do
  let motif : Draw.DrawM Unit := do
    Draw.DrawScope.drawCircle (.solid (Color.hex 0xFFBB86FC)) ⟨20, 24⟩ 12
    Draw.DrawScope.drawCircle (.solid (Color.hex 0xFF03DAC6)) ⟨40, 24⟩ 12
  Row (horizontalArrangement := .spacedBy 12) (verticalAlignment := .centerVertically) do
    Box (modifier := (Modifier.size 60 48).drawBehind motif)
    Box (modifier := (Modifier.blur 8 |>.size 60 48).drawBehind motif)
    Text "sharp · blurred (GPU)"

/-- The dark-theme strip: the same controls on the dark baseline palette. -/
composable def darkSection (checked : MutableState Bool)
    (on : MutableState Bool) : Composable Unit := do
  let c ← checked.get
  let o ← on.get
  MaterialTheme (colors := .dark) do
    Surface (modifier := Modifier.fillMaxWidth) (shape := .rounded 12) do
      Row (modifier := Modifier.padding (all := 12)) (horizontalArrangement := .spacedBy 8)
          (verticalAlignment := .centerVertically) do
        Text "Dark"
        Button (pure ()) (Text "Filled")
        Checkbox c checked.set
        Switch o on.set

/-- The gallery screen (see the module docstring). -/
composable def widgetsUi : Composable Unit := do
  let clicks ← remember (mutableStateOf (0 : Nat))
  let checked ← remember (mutableStateOf true)
  let choice ← remember (mutableStateOf (0 : Nat))
  let on ← remember (mutableStateOf false)
  let amount ← remember (mutableStateOf (0.5 : Float32))
  MaterialTheme do
    Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 10) do
      Text "Material widgets" (style := { fontSize := 22 })
      buttonsSection clicks
      HorizontalDivider
      togglesSection checked choice on
      HorizontalDivider
      progressSection amount
      HorizontalDivider
      imagesSection
      HorizontalDivider
      gradientsSection
      HorizontalDivider
      transformsSection
      HorizontalDivider
      effectsSection
      HorizontalDivider
      darkSection checked on

end Demos.Widgets

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose widgets" 480 700 Demos.Widgets.widgetsUi
    { clearColor := Compose.ColorScheme.light.surface }
