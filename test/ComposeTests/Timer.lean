import Compose
import ComposeTests.Harness
import Demos.Timer

/-!
# Timer demo behavior tests (`test/ComposeTests/Timer.lean`)

The 7GUIs *Timer* demo (`Demos/Timer.lean`) driven through the MT framework
with a **frozen clock**: `advanceTimeBy` supplies every millisecond of elapsed
time, so ticking is proven deterministically with zero real-time sleeps. We
inject the `elapsed`/`duration` states into `timerBody` and read them back
directly, and assert the gauge through its published range value.
-/

namespace Tests.Timer
open Compose Compose.Test Tests.Harness Demos.Timer

/-- Elapsed grows with the fake clock, clamps at the duration, and then stops. -/
private def ticksAndStops : IO Unit := do
  let elapsed ← mutableStateOf (0.0 : Float32)
  let duration ← mutableStateOf (1000.0 : Float32)
  runComposeTest (content := timerBody elapsed duration) do
    checkEq "starts at 0" (← elapsed.get) 0.0
    assertRangeValue (.tag "gauge") 0.0
    -- Half a second of fake time: elapsed grows but is still below duration.
    advanceTimeBy 500
    let mid ← elapsed.get
    check "grew past 0" (decide (0 < mid))
    check "still below duration" (decide (mid < 1000))
    -- Past the duration: elapsed is clamped to it and the gauge is full.
    advanceTimeBy 1000
    checkEq "clamped to duration" (← elapsed.get) 1000.0
    assertRangeValue (.tag "gauge") 1.0
    -- Stopped: more fake time does not move elapsed.
    let stopped ← elapsed.get
    advanceTimeBy 1000
    checkEq "stays stopped at duration" (← elapsed.get) stopped

/-- Raising the duration resumes a stopped timer; lowering it below the
elapsed clamps the gauge to full; Reset (the real button) zeroes it and lets
it run again. -/
private def resumeClampReset : IO Unit := do
  let elapsed ← mutableStateOf (0.0 : Float32)
  let duration ← mutableStateOf (1000.0 : Float32)
  runComposeTest (content := timerBody elapsed duration) do
    -- Run to completion.
    advanceTimeBy 1500
    checkEq "finished at duration" (← elapsed.get) 1000.0
    -- Raising the duration above the stopped elapsed resumes ticking.
    duration.set 3000.0
    advanceTimeBy 500
    let resumed ← elapsed.get
    check "resumed past the old duration" (decide (1000 < resumed))
    check "below the new duration" (decide (resumed < 3000))
    -- Lowering the duration below elapsed clamps the gauge full and stops.
    duration.set 200.0
    assertRangeValue (.tag "gauge") 1.0
    let frozen ← elapsed.get
    advanceTimeBy 500
    checkEq "stopped after lowering below elapsed" (← elapsed.get) frozen
    -- Reset zeroes elapsed through the real button, and it runs again.
    click (.tag "reset")
    checkEq "reset to 0" (← elapsed.get) 0.0
    advanceTimeBy 100
    check "runs again after reset" (decide (0 < (← elapsed.get)))

/-- The duration slider is wired to the duration state (real drag through the
router). -/
private def sliderDrivesDuration : IO Unit := do
  let elapsed ← mutableStateOf (0.0 : Float32)
  let duration ← mutableStateOf (0.0 : Float32)
  runComposeTest (content := timerBody elapsed duration) do
    checkEq "duration starts at 0" (← duration.get) 0.0
    -- A rightward drag raises the duration off zero.
    drag (.tag "duration") ⟨80, 0⟩
    check "drag raised the duration" (decide (0 < (← duration.get)))

/-- The Timer group. -/
def run : IO Unit := do
  scenario "ticksAndStops" ticksAndStops
  scenario "resumeClampReset" resumeClampReset
  scenario "sliderDrivesDuration" sliderDrivesDuration

end Tests.Timer
