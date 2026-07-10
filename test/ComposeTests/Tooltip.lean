import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Tooltip test group (`test/ComposeTests/Tooltip.lean`)

MT coverage of `TooltipArea`/`Tooltip` on the frozen clock: hover arms the
delay but shows nothing until it elapses; exit and press hide immediately and
cancel a pending timer; re-entering restarts the delay from zero.
-/

namespace Tests.Tooltip
open Compose Compose.Test Tests.Harness

/-- A `Tooltip` over a small target, with empty space below to hover away to.
`delayMs` is short so the frozen clock only has to step a little. -/
private def content : Composable Unit :=
  Column do
    Tooltip "Help text" (delayMs := 300) (modifier := Modifier.testTag "target")
      (Box (modifier := Modifier.size 60 30))
    Spacer (Modifier.size 120 120 |>.testTag "empty")

/-! ## Delay: nothing until the timer elapses, then the tooltip shows -/

private def delayThenShow : IO Unit := runComposeTest content do
  assertMissing (.text "Help text")
  moveTo (.tag "target")
  -- Timer armed on enter, but the clock is frozen: still hidden.
  assertMissing (.text "Help text")
  advanceTimeBy 200
  assertMissing (.text "Help text")     -- still short of the 300 ms delay
  advanceTimeBy 200                     -- now past it
  assertExists (.text "Help text")

/-! ## Exit hides immediately -/

private def exitHides : IO Unit := runComposeTest content do
  moveTo (.tag "target")
  advanceTimeBy 400
  assertExists (.text "Help text")
  -- Hovering away delivers exit to the content, hiding the tooltip.
  moveTo (.tag "empty")
  assertMissing (.text "Help text")

/-! ## A press hides it -/

private def pressHides : IO Unit := runComposeTest content do
  moveTo (.tag "target")
  advanceTimeBy 400
  assertExists (.text "Help text")
  click (.tag "target")                 -- the press hides it at once
  assertMissing (.text "Help text")

/-! ## A pending timer is cancelled by exit; re-entering restarts the delay -/

private def reEnterRestarts : IO Unit := runComposeTest content do
  moveTo (.tag "target")
  advanceTimeBy 200                     -- partway into the delay
  assertMissing (.text "Help text")
  moveTo (.tag "empty")                 -- exit cancels the pending timer
  advanceTimeBy 200                     -- the cancelled timer must not fire
  assertMissing (.text "Help text")
  -- Re-enter: a fresh 300 ms delay, so 200 ms is still too short…
  moveTo (.tag "target")
  advanceTimeBy 200
  assertMissing (.text "Help text")
  advanceTimeBy 200                     -- …and now the restarted delay elapses
  assertExists (.text "Help text")

/-- The Tooltip group. -/
def run : IO Unit := do
  scenario "delayThenShow" delayThenShow
  scenario "exitHides" exitHides
  scenario "pressHides" pressHides
  scenario "reEnterRestarts" reEnterRestarts

end Tests.Tooltip
