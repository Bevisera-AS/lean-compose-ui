import Compose

/-!
# Timer demo (`lake exe demo-timer`)

The 7GUIs *Timer* task (https://eugenkiss.github.io/7guis/tasks): a gauge
showing elapsed time as a fraction of a chosen duration, a numeric "12.4s"
label, a duration `Slider` (0–30 s), and a `Reset` button.

Elapsed time advances in real time and **stops** when it reaches the
duration; moving the slider takes effect immediately — raising the duration
above a stopped elapsed resumes ticking, lowering it below clamps the gauge
to full. `Reset` sets elapsed back to zero.

Ticking is driven by a `LaunchedEffect` that accumulates *frame-clock deltas*
(never the wall clock), so the MT test suite (`test/ComposeTests/Timer.lean`)
drives it deterministically with `advanceTimeBy` — no real-time sleeps.
Headless: `SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-timer`.
-/

namespace Demos.Timer
open Compose

/-- The gauge fill as a fraction in `[0,1]`: `elapsed / duration`, clamped.
A non-positive duration reads as full (the timer is trivially "done"). Pure —
`#guard`ed below. -/
def gaugeFraction (elapsedMs durationMs : Float32) : Float32 :=
  if durationMs ≤ 0 then 1
  else
    let f := elapsedMs / durationMs
    if f > 1 then 1 else f

#guard gaugeFraction 0 30000 == 0
#guard gaugeFraction 15000 30000 == 0.5
#guard gaugeFraction 30000 30000 == 1
#guard gaugeFraction 40000 30000 == 1   -- duration lowered below elapsed → full
#guard gaugeFraction 5 0 == 1           -- zero duration → full

/-- Render a millisecond count as a one-decimal seconds label, e.g. `"12.4s"`.
Pure — `#guard`ed below. -/
def formatSeconds (ms : Nat) : String :=
  let ds := ms / 100          -- tenths of a second (truncated)
  s!"{ds / 10}.{ds % 10}s"

#guard formatSeconds 0 == "0.0s"
#guard formatSeconds 999 == "0.9s"
#guard formatSeconds 12400 == "12.4s"
#guard formatSeconds 30000 == "30.0s"

/-- The maximum selectable duration, in milliseconds (30 s). -/
def maxDurationMs : Float32 := 30000

/-- The tick loop: on every frame, add the frame-clock delta to `elapsed`
while it is below `duration`, clamping so ticking never overshoots the
duration. Reads only the injected frame clock (`awaitFrame`'s nanos), so the
MT clock controls it exactly. Recurses until `elapsed ≥ duration`, then ends —
the enclosing `LaunchedEffect` also stops subscribing to frames, so a finished
timer idles at 0% CPU. -/
private partial def runTicks (elapsed duration : MutableState Float32)
    (lastNs : UInt64) : UiTask Unit := do
  let nowNs ← UiTask.awaitFrame
  let e ← elapsed.get
  let d ← duration.get
  if e < d then
    let dtMs := ((nowNs - lastNs).toFloat / 1.0e6).toFloat32
    let e' := e + dtMs
    elapsed.set (if e' > d then d else e')
    runTicks elapsed duration nowNs

/-- The timer screen, factored on injected state so the MT suite can drive and
inspect it directly. -/
composable def timerBody (elapsed duration : MutableState Float32) :
    Composable Unit := do
  let e ← elapsed.get
  let d ← duration.get
  let running := decide (e < d)
  -- Relaunch the tick loop whenever `running` flips: raising the duration
  -- above a stopped elapsed resumes it; reaching the duration stops it.
  LaunchedEffect running do
    if running then
      let t0 ← UiTask.awaitFrame
      runTicks elapsed duration t0
  Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12) do
    Text "Timer" (style := { fontSize := 22 })
    Text "Elapsed time"
    LinearProgressIndicator (some (gaugeFraction e d))
      (modifier := Modifier.testTag "gauge" |>.fillMaxWidth)
    Text (formatSeconds e.toUInt32.toNat)
      (modifier := Modifier.testTag "elapsed-label")
    Text s!"Duration: {formatSeconds d.toUInt32.toNat}"
    Slider d duration.set (valueRange := (0, maxDurationMs))
      (modifier := Modifier.testTag "duration" |>.fillMaxWidth)
    Button (elapsed.set 0) (modifier := Modifier.testTag "reset") (Text "Reset")

/-- The Timer demo screen (see the module docstring). -/
composable def timerUi : Composable Unit := do
  let elapsed ← remember (mutableStateOf (0.0 : Float32))
  let duration ← remember (mutableStateOf (15000.0 : Float32))
  MaterialTheme (timerBody elapsed duration)

end Demos.Timer
