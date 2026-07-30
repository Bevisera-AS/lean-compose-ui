import Compose
import ComposeTests.Harness
import Demos.Gallery

/-!
# Gallery launcher tests (`test/ComposeTests/Gallery.lean`)

MT behavior tests for `Demos/Gallery.lean`. The screen is mounted with a
**recording** launch callback (never a real `IO.Process.spawn`), so clicking a
row's Launch button is observable without forking children.
-/

namespace Tests.Gallery
open Compose Compose.Test Tests.Harness

/-- Every registered demo gets a row with a launchable button, and the header
is present. -/
private def rowsExist : IO Unit := do
  let launched ← IO.mkRef (#[] : Array String)
  runComposeTest
    (Demos.Gallery.galleryUi (fun exe => launched.modify (·.push exe)))
    (width := 520) (height := 640)
    do
      assertExists (.text "compose-ui demos")
      for entry in Demos.Gallery.demos do
        assertExists (.tag s!"launch-{entry.exe}")

/-- Clicking a row's Launch button fires the injected launch action with that
demo's exe name (and nothing else). -/
private def clickLaunches : IO Unit := do
  let launched ← IO.mkRef (#[] : Array String)
  runComposeTest
    (Demos.Gallery.galleryUi (fun exe => launched.modify (·.push exe)))
    (width := 520) (height := 640)
    do
      -- The first rows sit inside the viewport (later rows scroll off and are
      -- unhittable); one click each, checking the recorded exe names.
      click (.tag "launch-demo-widgets")
      checkEq "launch fires exe" (← launched.get) #["demo-widgets"]
      click (.tag "launch-demo-overlays")
      checkEq "second launch appends" (← launched.get) #["demo-widgets", "demo-overlays"]

/-- The Gallery group. -/
def run : IO Unit := do
  scenario "rows exist" rowsExist
  scenario "click launches" clickLaunches

end Tests.Gallery
