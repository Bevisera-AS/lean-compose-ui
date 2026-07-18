module

public import Compose.Ui.Input.Pointer
public meta import Compose.Ui.Input.Pointer

public section

namespace Compose

/-!
# Input recording (`Compose/Ui/Input/Record.lean`)

The capture half of the real-input regression vehicle: an `InputRecorder`
dumps every already-translated `PointerEvent` reaching
`InputManager.pointerEvent` — plus a mark for each frame-clock tick — to a
JSONL file, so real on-device touch streams (with their genuine fractional
coordinates, batched-sample timing, and delivery jitter) can be replayed
through the router in the headless suite. Headless rigs and injected swipes
are integer-exact and batch-free; the bug class this exists for (Float32
rounding dust, velocity-tracker jitter) only occurs under real fingers.

Enabled by `installInput` when `COMPOSE_INPUT_RECORD=<path>` is set; the
replay reader lives in the test suite (`test/ComposeTests/Replay.lean`),
fixtures under `assets/test/input/`.

Format — one JSON object per line:
- header (first line): `{"v":1,"w":<px>,"h":<px>,"density":<scale>}` —
  render-pixel window size (the recorded coordinate space) and display
  density at capture time.
- event: `{"t":<ns>,"e":"press","x":…,"y":…,"pid":…,"btn":…,"clicks":…,
  "sx":…,"sy":…,"zoom":…,"mods":…}` — the `PointerEvent` data fields;
  `btn` is `MouseButton.val` (`0` = none), `mods` is `Keymod.val`. The
  per-dispatch behavior closures (`consume`/`steal`/…) are not data and are
  not recorded.
- frame: `{"t":<ns>,"e":"frame"}` — the loop ticked the frame clock at `t`
  (same `Sdl.getTicksNS` base as SDL event timestamps), so replays can run
  animation steps on the captured cadence.

Floats print in Lean's fixed 6-decimal form. That is lossless here: at
render-px magnitudes (< ~10⁴) a `Float32` ulp is ≥ 2.4e-4, far above the
1e-6 print grid, so the original value is always the nearest `Float32` to
the printed decimal and the reader recovers it exactly — the rounding-dust
fractions this vehicle exists to preserve survive the round trip.
-/

/-- Serialization tag of a `PointerEventType` (the `"e"` field). -/
def PointerEventType.tag : PointerEventType → String
  | .press => "press"
  | .release => "release"
  | .move => "move"
  | .scroll => "scroll"
  | .enter => "enter"
  | .exit => "exit"
  | .pinch => "pinch"

/-- Inverse of `PointerEventType.tag` (the replay reader's side). -/
def PointerEventType.ofTag? : String → Option PointerEventType
  | "press" => some .press
  | "release" => some .release
  | "move" => some .move
  | "scroll" => some .scroll
  | "enter" => some .enter
  | "exit" => some .exit
  | "pinch" => some .pinch
  | _ => none

#guard PointerEventType.ofTag? (PointerEventType.press.tag) == some .press
#guard PointerEventType.ofTag? (PointerEventType.exit.tag) == some .exit
#guard PointerEventType.ofTag? (PointerEventType.pinch.tag) == some .pinch
#guard PointerEventType.ofTag? "frame" == none

/-- Records translated pointer events and frame-clock ticks to a JSONL file
(see the module doc for the format). Create via `InputRecorder.create`;
`installInput` wires one up under `COMPOSE_INPUT_RECORD`. -/
structure InputRecorder where
  handle : IO.FS.Handle

namespace InputRecorder

/-- A `Float32` as a JSON number (Lean's fixed 6-decimal print — lossless at
render-px magnitudes, see the module doc). -/
private def f32 (x : Float32) : String :=
  toString x.toFloat

#guard f32 55.108765 == "55.108765"
#guard f32 (-3.5) == "-3.500000"
#guard f32 0 == "0.000000"

/-- The header line: recorded coordinate space (render px) and density. -/
def headerLine (w h : Int32) (density : Float32) : String :=
  s!"\{\"v\":1,\"w\":{w},\"h\":{h},\"density\":{f32 density}}"

#guard headerLine 1344 2992 2.625 == "{\"v\":1,\"w\":1344,\"h\":2992,\"density\":2.625000}"

/-- One recorded `PointerEvent` (data fields only). -/
def eventLine (ev : PointerEvent) : String :=
  let btn := match ev.button with
    | some b => b.val
    | none => 0
  s!"\{\"t\":{ev.timestamp},\"e\":\"{ev.eventType.tag}\",\"x\":{f32 ev.position.x},\"y\":{f32 ev.position.y},\"pid\":{ev.pointerId},\"btn\":{btn},\"clicks\":{ev.clicks},\"sx\":{f32 ev.scrollDelta.x},\"sy\":{f32 ev.scrollDelta.y},\"zoom\":{f32 ev.zoomDelta},\"mods\":{ev.mods.val}}"

#guard eventLine { eventType := .press, position := ⟨55.108765, 60.5⟩, pointerId := 1,
                   button := some .left, clicks := 1, timestamp := 123456789 }
  == "{\"t\":123456789,\"e\":\"press\",\"x\":55.108765,\"y\":60.500000,\"pid\":1,\"btn\":1,\"clicks\":1,\"sx\":0.000000,\"sy\":0.000000,\"zoom\":1.000000,\"mods\":0}"
#guard eventLine { eventType := .move, position := ⟨0.25, 3000.000244⟩, pointerId := 3,
                   timestamp := 42 }
  == "{\"t\":42,\"e\":\"move\",\"x\":0.250000,\"y\":3000.000244,\"pid\":3,\"btn\":0,\"clicks\":0,\"sx\":0.000000,\"sy\":0.000000,\"zoom\":1.000000,\"mods\":0}"

/-- One frame-clock tick mark. -/
def frameLine (tNs : UInt64) : String :=
  s!"\{\"t\":{tNs},\"e\":\"frame\"}"

#guard frameLine 123 == "{\"t\":123,\"e\":\"frame\"}"

/-- Open `path` (truncating) and write the header. -/
def create (path : String) (w h : Int32) (density : Float32) : IO InputRecorder := do
  let handle ← IO.FS.Handle.mk path .write
  handle.putStrLn (headerLine w h density)
  handle.flush
  return { handle }

/-- Record one translated pointer event. Flushed per line — capture sessions
end in a force-stop, not a clean shutdown. -/
def event (r : InputRecorder) (ev : PointerEvent) : IO Unit := do
  r.handle.putStrLn (eventLine ev)
  r.handle.flush

/-- Record a frame-clock tick. -/
def frame (r : InputRecorder) (tNs : UInt64) : IO Unit := do
  r.handle.putStrLn (frameLine tNs)
  r.handle.flush

end InputRecorder

end Compose

end
