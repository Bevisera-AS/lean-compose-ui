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
      (content := do
        Text "Counter" (style := { fontSize := 22 })
        TextFieldS (toString n) (fun _ => pure ()) (enabled := false)
          (modifier := Modifier.testTag "count")
        Button (count.modify (· + 1)) (modifier := Modifier.testTag "count-btn")
          (content := Text "Count")))

end Demos.Counter
