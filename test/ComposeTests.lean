import Compose
import ComposeTests.Harness
import ComposeTests.Runtime
import ComposeTests.MacroSuite
import ComposeTests.Draw
import ComposeTests.Layout
import ComposeTests.Scheduler
import ComposeTests.App

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
  Harness.group "App" App.run
  Harness.summary
