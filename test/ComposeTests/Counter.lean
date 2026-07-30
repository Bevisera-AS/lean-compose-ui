import Compose
import ComposeTests.Harness
import Demos.Counter

/-!
# Counter demo tests (`test/ComposeTests/Counter.lean`)

MT behavior tests for `Demos/Counter.lean`, driving the real screen: the
read-only field starts at `0` and each "Count" click increments it. The demo
composable is imported and mounted directly, so the tests exercise the exact
UI the executable ships.
-/

namespace Tests.Counter
open Compose Compose.Test Tests.Harness

/-- Clicking "Count" increments the read-only field. -/
private def increment : IO Unit := runComposeTest
  Demos.Counter.counterUi
  (width := 360) (height := 280)
  do
    assertTextEquals (.tag "count") "0"
    click (.tag "count-btn")
    assertTextEquals (.tag "count") "1"
    click (.tag "count-btn")
    assertTextEquals (.tag "count") "2"
    -- The field is read-only: clicking it never changes the value.
    click (.tag "count")
    assertTextEquals (.tag "count") "2"

/-- The Counter group. -/
def run : IO Unit := do
  scenario "increment" increment

end Tests.Counter
