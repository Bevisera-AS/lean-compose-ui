import Lean
import Compose
import ComposeTests.Harness

/-!
# Replay group (`test/ComposeTests/Replay.lean`)

The playback half of the real-input regression vehicle: loads JSONL
recordings written by `InputRecorder` (`COMPOSE_INPUT_RECORD` — see
`Compose/Ui/Input/Record.lean`) from `assets/test/input/` and drives them
through an `InputManager` over a fake-clock scheduler, event timestamps and
frame-tick marks preserved. Real finger streams carry what synthetic tests
cannot fake — fractional coordinates whose Float32 sums leave rounding dust,
batched-sample timing, delivery jitter — so these replays regress the bug
class only real touch input triggers (the dust band latch and the velocity
spikes from the first on-glass round).

Assertions are invariants, not pixel-exact outcomes: the overscroll band
stays zero while the scroll value is strictly in range (the dust latch
violated this), no frame tick moves the value implausibly far (the 426k px/s
velocity bug moved ~6800 px in one tick; a hard flick moves ~70), the state
settles at rest, and the gesture actually scrolled.
-/

namespace Tests.Replay
open Compose Tests.Harness

/-- Milliseconds → the scheduler's nanosecond clock. -/
private def ms (n : UInt64) : UInt64 := n * 1_000_000

/-- A scheduler over a settable fake clock. -/
private def fakeSched : IO (Scheduler × IO.Ref UInt64) := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  return (s, clock)

/-- A leaf `Layout` (no children, sized by its modifier). -/
private def leaf (m : Modifier) : Composable Unit := Layout m .leaf

/-- Composition + input manager over a fake clock at the recording's size
(the `Input.lean` rig, sized from the fixture header). -/
private structure Rig where
  s : Scheduler
  clock : IO.Ref UInt64
  root : LayoutNode
  comp : Composition
  im : InputManager

private def rig (content : Composable Unit) (w h : Int32) : IO Rig := do
  let (s, clock) ← fakeSched
  let root ← LayoutNode.create
  let comp ← Composition.create (LayoutNode.applier root)
    (CompositionLocalProvider LocalScheduler (some s) content)
  let _ ← root.remeasure { maxWidth := w, maxHeight := h }
  let im ← InputManager.create root { set := fun _ => pure () } (sched := some s)
  s.runDue 0
  return { s, clock, root, comp, im }

/-- Locate a committed test asset (current dir, then the executable's
ancestors — the walk `Image.lean` uses). -/
private def assetPath (rel : String) : IO (Option String) := do
  let mut roots : Array System.FilePath := #[← IO.currentDir]
  if let some d ← try some <$> IO.appDir catch _ => pure none then
    let mut cur := d
    for _ in [0:5] do
      roots := roots.push cur
      cur := cur.parent.getD cur
  for r in roots do
    if ← (r / rel).pathExists then
      return some (r / rel).toString
  return none

/-! ## Fixture format -/

private structure RecHeader where
  w : Int32
  h : Int32
  density : Float32

private inductive RecLine where
  | event (ev : PointerEvent)
  | frame (t : UInt64)

private structure Recording where
  header : RecHeader
  lines : Array RecLine

private def getNat (j : Lean.Json) (k : String) : Except String Nat :=
  j.getObjValAs? Nat k

private def getF32 (j : Lean.Json) (k : String) : Except String Float32 :=
  (·.toFloat32) <$> j.getObjValAs? Float k

/-- One non-header line: an `InputRecorder.eventLine`/`frameLine` object. -/
private def parseLine (j : Lean.Json) : Except String RecLine := do
  let t := (← getNat j "t").toUInt64
  let tag ← j.getObjValAs? String "e"
  if tag == "frame" then return .frame t
  let some eventType := PointerEventType.ofTag? tag
    | throw s!"unknown event tag {tag}"
  let btn := (← getNat j "btn").toUInt8
  return .event
    { eventType
      position := ⟨← getF32 j "x", ← getF32 j "y"⟩
      pointerId := (← getNat j "pid").toUInt64
      button := if btn == 0 then none else some ⟨btn⟩
      clicks := (← getNat j "clicks").toUInt8
      scrollDelta := ⟨← getF32 j "sx", ← getF32 j "sy"⟩
      zoomDelta := ← getF32 j "zoom"
      mods := ⟨(← getNat j "mods").toUInt16⟩
      timestamp := t }

private def parseRecording (text : String) : Except String Recording := do
  let lines := text.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  match lines with
  | [] => throw "empty recording"
  | headerLine :: rest =>
    let hj ← Lean.Json.parse headerLine
    let v ← getNat hj "v"
    unless v == 1 do throw s!"unsupported recording version {v}"
    let header : RecHeader :=
      { w := (← getNat hj "w").toInt32
        h := (← getNat hj "h").toInt32
        density := ← getF32 hj "density" }
    let mut parsed := #[]
    for l in rest do
      parsed := parsed.push (← parseLine (← Lean.Json.parse l))
    return { header, lines := parsed }

private def Recording.load (rel : String) : IO Recording := do
  let some path ← assetPath rel
    | throw (IO.userError s!"replay fixture not found: {rel}")
  match parseRecording (← IO.FS.readFile path) with
  | .ok rec => return rec
  | .error e => throw (IO.userError s!"replay fixture {rel}: {e}")

/-! ## Replay driver -/

/-- Frame ticks a replay appends past the recording's end so in-flight
animations (a fling the capture cut short, a settle that needs more steps
than the recorded run) reach rest before the final assertions. -/
private def settleTickCap : Nat := 600

/-- Drive a recording through the rig: each line advances the fake clock to
its timestamp, events dispatch through `InputManager.pointerEvent`, frame
marks tick the frame clock; then keep ticking at 16 ms until the scheduler
has no frame work. `probe` runs after every event *and* tick — a drag with
no live animation records no frame marks, so per-event probing is what sees
a mid-gesture invariant break. -/
private def Recording.replay (rec : Recording) (r : Rig)
    (probe : IO Unit := pure ()) : IO Unit := do
  let mut last : UInt64 := 0
  for line in rec.lines do
    match line with
    | .event ev =>
      r.clock.set ev.timestamp
      r.s.runDue ev.timestamp
      let _ ← r.im.pointerEvent ev
      probe
      last := ev.timestamp
    | .frame t =>
      r.clock.set t
      r.s.runDue t
      r.s.tickFrame t
      probe
      last := t
  let mut t := last
  for _ in [0:settleTickCap] do
    unless ← r.s.hasFrameWork do break
    t := t + ms 16
    r.clock.set t
    r.s.runDue t
    r.s.tickFrame t
    probe

/-! ## Scroll-invariant probes -/

/-- Accumulated over a scroll replay by `replayScroll`'s per-tick probe. -/
private structure ScrollStats where
  /-- Band observed non-zero while the value was strictly in range (the dust
  latch's signature). -/
  bandDirtyInRange : Bool := false
  /-- Largest per-step (event or frame tick) value movement, px (a velocity
  spike's signature — hard real flicks move ~70 px/frame, the two-axes bug
  moved ~6800). -/
  maxStepDelta : Float32 := 0
  /-- Largest scroll value reached. -/
  maxValue : Float32 := 0

/-- Replay a fixture against a vertical scroll rig sized from its header
(content 6× the viewport) and collect the invariant stats. -/
private def replayScroll (rel : String) : IO (ScrollState × ScrollStats) := do
  let rec ← Recording.load rel
  let st ← ScrollState.create
  let w : Dp := ⟨rec.header.w.toFloat32⟩
  let h : Dp := ⟨rec.header.h.toFloat32⟩
  let r ← rig
    (Box do
      Box (modifier := Modifier.size w h |>.verticalScroll st) do
        leaf (Modifier.size w (h * (6 : Float32))))
    rec.header.w rec.header.h
  let stats ← IO.mkRef ({} : ScrollStats)
  let lastValue ← IO.mkRef (0 : Float32)
  rec.replay r (probe := do
    let v ← st.value
    let o ← st.overscroll
    let max ← st.maxValue
    let prev ← lastValue.get
    lastValue.set v
    stats.modify fun s =>
      { bandDirtyInRange := s.bandDirtyInRange || (o != 0 && v > 0 && v < max)
        maxStepDelta := if (v - prev).abs > s.maxStepDelta then (v - prev).abs
                        else s.maxStepDelta
        maxValue := if v > s.maxValue then v else s.maxValue })
  return (st, ← stats.get)

/-- The shared invariant block every scroll fixture must satisfy. -/
private def checkScrollInvariants (tag : String) (st : ScrollState)
    (stats : ScrollStats) (minTravel : Float32) : IO Unit := do
  check s!"{tag}: band stays zero while in range" (!stats.bandDirtyInRange)
  check s!"{tag}: no per-step velocity spike ({stats.maxStepDelta})"
    (stats.maxStepDelta < 2000)
  check s!"{tag}: gesture scrolled (max {stats.maxValue})"
    (stats.maxValue ≥ minTravel)
  checkEq s!"{tag}: band settled at rest" (← st.overscroll) 0
  let v ← st.value
  check s!"{tag}: value settled in range ({v})" (v ≥ 0 && v ≤ (← st.maxValue))

/-! ## Tests -/

/-- Format→parse round trip through the real recorder strings. -/
private def roundTrip : IO Unit := do
  let ev : PointerEvent :=
    { eventType := .press, position := ⟨55.108765, 3000.000244⟩, pointerId := 3
      button := some .left, clicks := 1, mods := ⟨64⟩, timestamp := 123456789 }
  match Lean.Json.parse (InputRecorder.eventLine ev) >>= parseLine with
  | .error e => check s!"roundtrip: parse failed ({e})" false
  | .ok (.frame _) => check "roundtrip: not a frame" false
  | .ok (.event p) => do
    check "roundtrip: type" (p.eventType == .press)
    check "roundtrip: exact position"
      (p.position.x == ev.position.x && p.position.y == ev.position.y)
    checkEq "roundtrip: pid" p.pointerId 3
    check "roundtrip: button" (p.button == some .left)
    checkEq "roundtrip: clicks" p.clicks 1
    check "roundtrip: mods" (p.mods.val == 64)
    checkEq "roundtrip: timestamp" p.timestamp 123456789
  match Lean.Json.parse (InputRecorder.frameLine 42) >>= parseLine with
  | .ok (.frame t) => checkEq "roundtrip: frame mark" t 42
  | _ => check "roundtrip: frame parse" false

/-- The hand-written smoke fixture: format-complete (header, fractional
coordinates, a finger stream, frame marks) so loader and driver are covered
before any device capture lands. -/
private def smokeDrag : IO Unit := do
  let rec ← Recording.load "assets/test/input/smoke-drag.jsonl"
  checkEq "smoke: header size" (rec.header.w, rec.header.h) (200, 200)
  check "smoke: header density" (rec.header.density == 1.0)
  check "smoke: has lines" (rec.lines.size ≥ 8)
  let (st, stats) ← replayScroll "assets/test/input/smoke-drag.jsonl"
  checkScrollInvariants "smoke" st stats 40

/-- One real-Pixel fixture (Pixel 10 Pro, wireless-debug capture session,
2026-07-17) through the scroll rig + the shared invariant block. -/
private def pixelFixture (name : String) (minTravel : Float32) : IO Unit := do
  let (st, stats) ← replayScroll s!"assets/test/input/{name}"
  checkScrollInvariants name st stats minTravel

/-- The recorded regression fixtures — real finger streams with the
fractional coordinates and timing the synthetic tests can't fake.
Verified must-fail-pre-fix: with the `motionDust` collapse (Scroll.lean)
and the `minSegmentNs` guard (Velocity.lean) reverted, these replays fail
their invariants (see the fixture commit message). -/
private def pixelFixtures : IO Unit := do
  pixelFixture "pixel-slow-drag.jsonl" 100
  pixelFixture "pixel-flick.jsonl" 50
  pixelFixture "pixel-fling-chain.jsonl" 200
  pixelFixture "pixel-edge-stretch.jsonl" 50
  pixelFixture "pixel-scroll-session.jsonl" 200

/-- The Replay group. -/
def run : IO Unit := do
  roundTrip
  smokeDrag
  pixelFixtures
