import Compose

/-!
# Demo gallery (`lake exe gallery`)

The launcher screen: one row per registered demo (title + one-line blurb +
a **Launch** button) that spawns the demo's executable. The registry
(`demos`) is the single source of truth — `Main.lean`'s `--list` prints its
`exe` names (consumed by `scripts/smoke-demos.sh`) and the `Main.main` shim
mounts `galleryUi` with a real process-spawn callback.

The spawn action is a `launch : String → IO Unit` parameter rather than a
hard-wired `IO.Process.spawn`, so the MT suite
(`test/ComposeTests/Gallery.lean`) can inject a recording stub and assert on
launch clicks without forking children. The screen is static, so it
terminates under `COMPOSE_MAX_FRAMES`.
-/

namespace Demos.Gallery
open Compose

/-- One launcher entry: the executable name (`lake exe <exe>` /
`.lake/build/bin/<exe>`) plus its display title and blurb. -/
structure DemoEntry where
  /-- The `lean_exe` name — what `--list` prints and `launch` spawns. -/
  exe : String
  /-- Human title shown in the row. -/
  title : String
  /-- One-line description. -/
  desc : String
  deriving Repr

/-- The registered demos, in launcher (and `--list`) order. -/
def demos : List DemoEntry :=
  [ { exe := "demo-widgets",  title := "Material widgets",
      desc := "Buttons, toggles, slider, progress — light + dark." },
    { exe := "demo-overlays", title := "Overlays",
      desc := "Lazy list + scrollbar, dropdown menu, alert dialog." },
    { exe := "demo-counter",  title := "Counter",
      desc := "7GUIs #1 — a field and an increment button." },
    { exe := "demo-tempconv", title := "Temperature Converter",
      desc := "7GUIs #2 — bidirectionally synced C/F fields." },
    { exe := "demo-flight",   title := "Flight Booker",
      desc := "7GUIs #3 — mode combobox + validated dates." },
    { exe := "demo-timer",    title := "Timer",
      desc := "7GUIs #4 — gauge + duration slider, off the frame clock." },
    { exe := "demo-crud",     title := "CRUD",
      desc := "7GUIs #5 — filtered list + create/update/delete." },
    { exe := "demo-circles",  title := "Circle Drawer",
      desc := "7GUIs #6 — undo/redo canvas with a diameter dialog." },
    { exe := "demo-cells",    title := "Cells",
      desc := "7GUIs #7 — a virtualized spreadsheet with formulas." },
    { exe := "demo-desktop",  title := "Desktop components",
      desc := "Multi-window, menu bar, context menu, tooltips, system tray." },
    { exe := "demo-smoke",    title := "Smoke",
      desc := "Timers + frame clock + recomposition (M5 shell)." } ]

/-- One launcher row: title + blurb on the left, a tagged **Launch** button on
the right that fires `launch entry.exe`. -/
composable def demoRow (launch : String → IO Unit) (entry : DemoEntry) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Surface (Modifier.fillMaxWidth) (shape := .rounded 12)
    (color := colors.surfaceVariant) (content :=
    Row (Modifier.padding (all := 12)) (verticalAlignment := .centerVertically)
      (content := do
        Column (Modifier.weight 1) (verticalArrangement := .spacedBy 2)
          (content := do
            Text entry.title (style := { fontSize := 16, weight := .medium })
            Text entry.desc (style := { fontSize := 13 }))
        Button (launch entry.exe) (modifier := Modifier.testTag s!"launch-{entry.exe}")
          (content := Text "Launch")))

/-- The gallery screen: a scrollable, titled list of `demoRow`s with a
desktop scrollbar (auto-hides when idle). `launch` is the per-row spawn
action (production: fork the demo exe; tests: record it). -/
composable def galleryUi (launch : String → IO Unit) : Composable Unit := do
  let scroll ← rememberScrollState
  MaterialTheme (content :=
    Box (Modifier.fillMaxSize) (content := do
      Column ((Modifier.fillMaxSize).padding (all := 16) |>.verticalScroll scroll)
        (verticalArrangement := .spacedBy 10) (content := do
          Text "compose-ui demos" (style := { fontSize := 24, weight := .bold })
          Text "Pick a demo to launch." (style := { fontSize := 14 })
          demos.forM (demoRow launch))
      VerticalScrollbar scroll (Modifier.align .topEnd |>.fillMaxHeight)))

end Demos.Gallery
