import Compose

/-!
# Counter demo (`lake exe demo-counter`)

The first 7GUIs task (<https://eugenkiss.github.io/7guis/tasks#counter>): a
read-only field showing a count that starts at `0`, and a "Count" button that
increments it. The framework's hello-world — deliberately tiny. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-counter`.
-/

namespace Demos.Counter
open Compose

/-- The Counter screen (see the module docstring). A disabled `TextFieldS`
plays the spec's read-only field; the `Button` increments the remembered
count. -/
composable def counterUi : Composable Unit := do
  let count ← remember (mutableStateOf (0 : Nat))
  let n ← count.get
  MaterialTheme (content :=
    Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12)
      (content := fun _ => do
        Text "Counter" (style := { fontSize := 22 })
        TextFieldS (toString n) (fun _ => pure ()) (enabled := false)
          (modifier := Modifier.testTag "count")
        Button (count.modify (· + 1)) (modifier := Modifier.testTag "count-btn")
          (content := Text "Count")))

/-- Headless-smoke frame pump: a fully static screen idles (presents no
frames), so under `COMPOSE_MAX_FRAMES` the loop would never reach its cap and
exit. When `enabled` (smoke runs only), an infinite transition keeps frame
work scheduled — mirrors the auto-driver in `Demos/Overlays.lean`. Draws
nothing; disabled (and thus inert) in interactive runs. -/
composable def smokePump (enabled : Bool) : Composable Unit := do
  if enabled then
    let it ← rememberInfiniteTransition
    let phase ← it.animateFloat 0 1 (.infiniteRepeatable (.tween 500 0 .linear))
    let _ ← phase.get
    pure ()

/-- The demo's window: the frame pump plus the screen. `smoke` is set from
`COMPOSE_MAX_FRAMES` by the entry point in `Demos/CounterMain.lean`. -/
composable def counterApp (smoke : Bool) : Composable Unit := do
  smokePump smoke
  counterUi

end Demos.Counter
