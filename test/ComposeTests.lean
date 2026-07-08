import Compose
import ComposeTests.Harness
import ComposeTests.Runtime
import ComposeTests.MacroSuite
import ComposeTests.Draw
import ComposeTests.Layout
import ComposeTests.Scheduler
import ComposeTests.Animation
import ComposeTests.App
import ComposeTests.Input
import ComposeTests.Text
import ComposeTests.Material
import ComposeTests.Overlay
import ComposeTests.TextField
import ComposeTests.UiTest
import ComposeTests.Timer
import ComposeTests.Crud

/-!
# Runtime test entry point

Groups register here as milestones land; pure logic is tested at compile time
with `#guard` next to the definitions instead. Run headless:
`SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test`
(`COMPOSE_TEST_GROUP=<Name>` runs a single group). The `Runtime` group needs
no SDL drivers at all.
-/

open Tests

def main : IO UInt32 := do
  Harness.group "Runtime" Runtime.run
  Harness.group "Macro" MacroSuite.run
  Harness.group "Draw" Draw.run
  Harness.group "Layout" Layout.run
  Harness.group "Scheduler" Scheduler.run
  Harness.group "Animation" Animation.run
  Harness.group "App" App.run
  Harness.group "Input" Input.run
  Harness.group "Text" Text.run
  Harness.group "Material" Material.run
  Harness.group "Overlay" Overlay.run
  Harness.group "TextField" TextField.run
  Harness.group "UiTest" UiTest.run
  Harness.group "Timer" Timer.run
  Harness.group "Crud" Crud.run
  Harness.summary
