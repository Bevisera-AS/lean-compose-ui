import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Overlay test group (`test/ComposeTests/Overlay.lean`)

M10's suites: scroll containers (wheel, clamping, pixel shift, nesting,
programmatic scroll), the desktop scrollbar (thumb geometry, drag, paging,
auto-hide, hover widening), `LazyColumn` virtualization (composition
counters, window shifts, keyed state survival, scroll range), and the
overlay system (`Popup` positioning/z-order/dismissal, `Dialog` scrim,
`DropdownMenu` + `ExposedDropdownMenuBox` interaction and keyboard nav).

Everything runs in the Material-group rig shape: a bootstrapped headless
window whose content composes under a **fake-clock scheduler**, synthetic
`Sdl.Event`s through `dispatchEvent`, deterministic animation via manual
`runDue`/`tickFrame`, and `readPixels` probes.
-/

namespace Tests.Overlay
open Compose Tests.Harness

/-- Test config: software renderer for stable `readPixels`, no vsync. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

private def L : ColorScheme := .light

/-- Whether an SDL pixel is within `tol` byte-steps of a framework color. -/
private def near (c : Sdl.Color) (e : Compose.Color) (tol : Nat := 4) : Bool :=
  let (r, g, b, _) := e.toBytes
  colorNear c r g b tol

/-- `fg` composited over opaque white (the test clear color). -/
private def overWhite (fg : Compose.Color) : Compose.Color :=
  fg.compositeOver .white

/-- `|x − y| ≤ tol` for runtime float checks. -/
private def approx (x y : Float32) (tol : Float32 := 0.6) : Bool := (x - y).abs ≤ tol

instance : ToString Float32 := ⟨fun x => toString x.toFloat⟩

/-! ## Rig -/

private structure ORig where
  ctx : WindowContext
  s : Scheduler
  clock : IO.Ref UInt64

/-- Bootstrap `content` under a fake-clock `LocalScheduler`, start the queued
coroutines, render the first frame. -/
private def oboot (content : Composable Unit) (w : Dp := 300) (h : Dp := 300) :
    IO ORig := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  let ctx ← bootstrap "compose-overlay-test" w h
    (CompositionLocalProvider LocalScheduler (some s) content) cfg
  let _ ← step ctx cfg
  s.runDue 0
  return { ctx, s, clock }

private def ORig.render (r : ORig) : IO Unit := do
  if ← r.ctx.needsFrame.get then
    let _ ← step r.ctx cfg

/-- Advance the fake clock by `dtMs`, run due coroutines, tick the frame
clock, render. -/
private def ORig.tick (r : ORig) (dtMs : UInt64) : IO Unit := do
  let t := (← r.clock.get) + dtMs * 1_000_000
  r.clock.set t
  r.s.runDue t
  r.s.tickFrame t
  r.render

/-- Settle: alternate render (recompose) and `runDue` a few times so chained
launches start (an effect that recomposes something that launches an
animation), tick 8 ms frames until the frame clock has no subscribers (cap
2.4 s fake time), render the final state. -/
private def ORig.settle (r : ORig) : IO Unit := do
  for _ in [0:4] do
    r.render
    r.s.runDue (← r.clock.get)
  let mut i := 0
  while (← r.s.hasFrameWork) && i < 300 do
    let t := (← r.clock.get) + 8 * 1_000_000
    r.clock.set t
    r.s.runDue t
    r.s.tickFrame t
    i := i + 1
  r.render
  r.render

private def ORig.pixel (r : ORig) (x y : Int32) : IO Sdl.Color := do
  (← (← r.ctx.sdlRenderer).readPixels).readPixel x y

private def ORig.send (r : ORig) (e : Sdl.Event) : IO Unit :=
  dispatchEvent r.ctx cfg e

private def ORig.press (r : ORig) (x y : Float32) : IO Unit :=
  r.send (.mouseButtonDown ⟨0, ⟨0⟩, ⟨0⟩, .left, true, 1, x, y⟩)

private def ORig.release (r : ORig) (x y : Float32) : IO Unit :=
  r.send (.mouseButtonUp ⟨0, ⟨0⟩, ⟨0⟩, .left, false, 1, x, y⟩)

private def ORig.click (r : ORig) (x y : Float32) : IO Unit := do
  r.press x y
  r.release x y

private def ORig.move (r : ORig) (x y : Float32) : IO Unit :=
  r.send (.mouseMotion ⟨0, ⟨0⟩, ⟨0⟩, .none, x, y, 0, 0⟩)

private def ORig.key (r : ORig) (k : Sdl.Keycode) : IO Unit :=
  r.send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, k, .none, 0, true, false⟩)

/-- Wheel at `(x, y)` with `dy` notches (positive = away from the user). -/
private def ORig.wheel (r : ORig) (x y dy : Float32) : IO Unit :=
  r.send (.mouseWheel ⟨0, ⟨0⟩, ⟨0⟩, 0, dy, .normal, x, y, 0, dy.toInt32⟩)

private def themed (content : Composable Unit) : Composable Unit :=
  MaterialTheme content

/-- A colored fixed-size block. -/
private def block (w h : Dp) (c : Compose.Color) : Composable Unit :=
  Spacer (Modifier.size w h |>.background c)

/-! ## Scroll -/

/-- Wheel scrolls (50 dp per notch — 50 px at this rig's 1× density), clamps
at both ends, and actually shifts the drawn content. -/
private def scrollWheel : IO Unit := do
  let st ← ScrollState.create
  let r ← oboot <| Column (modifier := Modifier.size 100 100 |>.verticalScroll st) do
    block 100 50 .red
    block 100 50 .green
    block 100 50 .blue
    block 100 50 .yellow
  check "scroll: starts at 0" ((← st.value) == 0)
  check "scroll: maxValue = content − viewport" ((← st.maxValue) == 100)
  check "scroll: viewport reported" ((← st.viewportSize) == 100)
  check "scroll: content reported" ((← st.contentSize) == 200)
  check "scroll: top pixel is the first block" (near (← r.pixel 10 10) .red)
  r.wheel 50 50 (-1)
  r.settle
  check s!"scroll: one notch down = 50 px ({← st.value})" ((← st.value) == 50)
  check "scroll: content pixel shifted (green now at the top)"
    (near (← r.pixel 10 10) .green)
  r.wheel 50 50 (-3)
  r.settle
  check s!"scroll: clamps at maxValue ({← st.value})" ((← st.value) == 100)
  check "scroll: bottom content visible" (near (← r.pixel 10 90) .yellow)
  r.wheel 50 50 5
  r.settle
  check s!"scroll: clamps at 0 ({← st.value})" ((← st.value) == 0)
  check "scroll: first block back on top" (near (← r.pixel 10 10) .red)
  -- Below the viewport the content is clipped away.
  check "scroll: clipped outside the viewport" (near (← r.pixel 10 150) .white)

/-- `scrollBy`/`scrollTo` clamp and report consumption; a content shrink
re-clamps the value. -/
private def scrollProgrammatic : IO Unit := do
  let st ← ScrollState.create
  let count ← MutableState.create (4 : Nat)
  let r ← oboot <| Column (modifier := Modifier.size 100 100 |>.verticalScroll st)
    (Tests.restartable 1 do
      let n ← count.get
      for i in [0:n] do
        keyed i (block 100 50 (if i % 2 == 0 then .red else .green)))
  checkEq "scrollBy: consumes what it can" (← st.scrollBy 30).toFloat 30.0
  check "scrollBy: value moved" ((← st.value) == 30)
  checkEq "scrollBy: clamped remainder consumed" (← st.scrollBy 1000).toFloat 70.0
  check "scrollBy: at max" ((← st.value) == 100)
  checkEq "scrollBy: at the end nothing is consumed" (← st.scrollBy 10).toFloat 0.0
  st.scrollTo 20
  check "scrollTo: exact" ((← st.value) == 20)
  st.scrollTo 5000
  check "scrollTo: clamps" ((← st.value) == 100)
  -- Shrink the content: 2 blocks = 100 px = viewport ⇒ max 0, value re-clamps.
  count.set 2
  r.settle
  check s!"scroll: content shrink re-clamps the value ({← st.value})"
    ((← st.value) == 0 && (← st.maxValue) == 0)
  check "scroll: shrunk content reported" ((← st.contentSize) == 100)

/-- An end-stopped inner scrollable lets the wheel bubble to the outer one. -/
private def scrollNested : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← oboot <| Column (modifier := Modifier.size 100 100 |>.verticalScroll outer) do
    Column (modifier := Modifier.size 100 60 |>.verticalScroll inner) do
      block 100 60 .red
      block 100 60 .green
    block 100 140 .blue
  check "nested: inner max" ((← inner.maxValue) == 60)
  check "nested: outer max" ((← outer.maxValue) == 100)
  r.wheel 50 30 (-1)
  r.settle
  check "nested: wheel over the inner scrolls it" ((← inner.value) == 50)
  check "nested: outer untouched" ((← outer.value) == 0)
  r.wheel 50 30 (-1)
  r.settle
  check "nested: partial consumption still consumes" ((← inner.value) == 60)
  check "nested: outer still untouched" ((← outer.value) == 0)
  r.wheel 50 30 (-1)
  r.settle
  check "nested: end-stopped inner bubbles to the outer" ((← outer.value) == 50)
  check "nested: inner stays clamped" ((← inner.value) == 60)

/-! ## Scrollbar -/

/-- Thumb pixels: proportional geometry, right-aligned 4 dp thumb. -/
private def scrollbarGeometry : IO Unit := do
  let st ← ScrollState.create
  let r ← oboot <| themed <| Box (modifier := Modifier.size 100 100 |>.background .white) do
    Column (modifier := Modifier.fillMaxSize |>.verticalScroll st) (block 100 400 .white)
    VerticalScrollbar st (Modifier.align .topEnd |>.fillMaxHeight)
  r.settle
  let thumb := overWhite (L.onSurface.withAlpha 0.4)
  -- track 100, viewport 100, content 400 ⇒ thumb 25 px at offset 0.
  check s!"scrollbar: thumb at the top ({showColor (← r.pixel 98 10)})"
    (near (← r.pixel 98 10) thumb 20)
  check "scrollbar: below the thumb is bare" (near (← r.pixel 98 60) .white)
  check "scrollbar: 4dp thumb leaves the strip's left half bare"
    (near (← r.pixel 93 10) .white)
  -- Scroll to the middle: offset (100−25) × 0.5 = 37.5 ⇒ thumb ≈ 38..62.
  st.scrollTo 150
  r.settle
  check "scrollbar: thumb moved proportionally" (near (← r.pixel 98 50) thumb 20)
  check "scrollbar: old position bare" (near (← r.pixel 98 10) .white)

/-- Dragging the thumb maps through the travel↔scroll ratio; track clicks
page by a viewport. -/
private def scrollbarDrag : IO Unit := do
  let st ← ScrollState.create
  let r ← oboot <| themed <| Box (modifier := Modifier.size 100 100 |>.background .white) do
    Column (modifier := Modifier.fillMaxSize |>.verticalScroll st) (block 100 400 .white)
    VerticalScrollbar st (Modifier.align .topEnd |>.fillMaxHeight)
  r.settle
  -- Thumb 25 px at 0; drag from inside it by 30 px: ratio = 300/75 = 4.
  r.press 96 10
  r.move 96 40
  r.settle
  check s!"scrollbar: drag maps to content scroll ({← st.value})"
    (approx (← st.value) 120)
  r.move 96 25
  r.release 96 25
  r.settle
  check s!"scrollbar: drag back ({← st.value})" (approx (← st.value) 60)
  -- Track click below the thumb pages down one viewport.
  st.scrollTo 0
  r.settle
  r.press 96 80
  r.release 96 80
  r.settle
  check s!"scrollbar: track click pages down ({← st.value})" ((← st.value) == 100)
  r.press 96 2
  r.release 96 2
  r.settle
  check s!"scrollbar: track click above pages up ({← st.value})" ((← st.value) == 0)

/-- Auto-hide after ~1 s of scheduler time; hovering shows it again and
widens the thumb to 8 dp. -/
private def scrollbarAutoHide : IO Unit := do
  let st ← ScrollState.create
  let r ← oboot <| themed <| Box (modifier := Modifier.size 100 100 |>.background .white) do
    Column (modifier := Modifier.fillMaxSize |>.verticalScroll st) (block 100 400 .white)
    VerticalScrollbar st (Modifier.align .topEnd |>.fillMaxHeight)
  r.settle
  let thumb := overWhite (L.onSurface.withAlpha 0.4)
  check "auto-hide: visible after boot activity" (near (← r.pixel 98 10) thumb 20)
  -- Advance past the hide delay (pointer far away): fades out.
  r.tick 1100
  r.settle
  check s!"auto-hide: faded after 1.1 s of scheduler time ({showColor (← r.pixel 98 10)})"
    (near (← r.pixel 98 10) .white)
  -- Scroll activity shows it again…
  r.wheel 50 50 (-1)
  r.settle
  check "auto-hide: scroll activity shows it" (near (← r.pixel 98 30) thumb 30)
  r.tick 1100
  r.settle
  check "auto-hide: fades again" (near (← r.pixel 98 30) .white)
  -- …and hovering shows and widens it: 8 dp reaches x = 92.
  r.move 96 30
  r.settle
  check "hover: shows the bar" (!(near (← r.pixel 98 30) .white))
  check s!"hover: widened thumb reaches 8dp ({showColor (← r.pixel 93 30)})"
    (!(near (← r.pixel 93 30) .white))
  r.move 20 20
  r.settle
  r.tick 1100
  r.settle
  check "hover: unhover + idle hides" (near (← r.pixel 98 30) .white)

/-! ## LazyColumn -/

/-- Only the visible window composes; scrolling composes entering items,
disposes leaving ones, keeps survivors' state, and skips their bodies. -/
private def lazyVirtualization : IO Unit := do
  let st ← ScrollState.create
  let composed ← IO.mkRef (#[] : Array Nat)   -- one entry per item body run
  let disposed ← IO.mkRef (#[] : Array Nat)
  let states ← IO.mkRef (#[] : Array (Nat × MutableState Nat))
  let item (i : Nat) : Composable Unit := do
    composed.modify (·.push i)
    let s ← remember (mutableStateOf (i * 100))
    states.modify (·.push (i, s))
    DisposableEffect i (do pure (disposed.modify (·.push i)))
    Spacer (Modifier.size 100 20)
  let r ← oboot <| Box (modifier := Modifier.size 100 100) do
    LazyColumn st (itemHeight := 20) (count := 100) item (modifier := Modifier.fillMaxWidth)
  r.settle
  check "lazy: total scroll range = count×height − viewport"
    ((← st.maxValue) == 100 * 20 - 100)
  let c0 ← composed.get
  checkEq "lazy: only the visible window composed (5 visible + 1 overscan)"
    (c0.qsort (· < ·) |>.toList.eraseDups) [0, 1, 2, 3, 4, 5]
  check s!"lazy: initial items composed exactly once ({c0})"
    (c0.toList.eraseDups.length == c0.size)
  -- Mutate item 5's remembered state, then scroll so 0..1 leave, 5 stays.
  if let some (_, s5) := (← states.get).findRev? (·.1 == 5) then
    s5.set 999
  composed.set #[]
  st.scrollTo 60   -- window: first = 3−1 = 2, lastEx = 8+1 = 9
  r.settle
  let c1 ← composed.get
  checkEq "lazy: scroll composes exactly the entering items"
    (c1.qsort (· < ·)) #[6, 7, 8]
  checkEq "lazy: leaving items disposed" ((← disposed.get).qsort (· < ·)) #[0, 1]
  -- Scroll back: 0..1 re-enter fresh; survivor 5 kept its state.
  composed.set #[]
  st.scrollTo 0
  r.settle
  checkEq "lazy: scrolling back re-composes the re-entering items"
    ((← composed.get).qsort (· < ·)) #[0, 1]
  let some (_, s5) := (← states.get).findRev? (·.1 == 5)
    | throw (IO.userError "item 5 state missing")
  checkEq "lazy: surviving item kept its remembered state" (← s5.cell.get) 999
  let some (_, s0) := (← states.get).findRev? (·.1 == 0)
    | throw (IO.userError "item 0 state missing")
  checkEq "lazy: re-entering item re-initialized" (← s0.cell.get) 0

/-- Swapping in a fresh `ScrollState` (same item size and count) must
re-derive the window from the NEW state: the derived-window key mixes in the
state identity, so the swap discards the old derivation instead of leaving
the window latched to the defunct state's reads. -/
private def lazyStateSwap : IO Unit := do
  let stA ← ScrollState.create
  let stB ← ScrollState.create
  let useB ← MutableState.create false
  let composed ← IO.mkRef (#[] : Array Nat)
  let item (i : Nat) : Composable Unit := do
    composed.modify (·.push i)
    Spacer (Modifier.size 100 20)
  let r ← oboot <| Box (modifier := Modifier.size 100 100)
    (Tests.restartable 1 do
      let st := if ← useB.get then stB else stA
      LazyColumn st (itemHeight := 20) (count := 100) item
        (modifier := Modifier.fillMaxWidth))
  r.settle
  useB.set true
  r.settle
  composed.set #[]
  stB.scrollTo 400   -- window with the new state: items 19..26
  r.settle
  check s!"lazy swap: scrolling the swapped-in state shifts the window ({← composed.get})"
    ((← composed.get).contains 20)
  checkEq "lazy swap: the new state's metrics are the live ones"
    (← stB.viewportSize).toFloat 100.0

/-- The lazy list scrolls with the wheel and draws the right items. -/
private def lazyWheelPixels : IO Unit := do
  let st ← ScrollState.create
  let r ← oboot <| Box (modifier := Modifier.size 100 100) do
    LazyColumn st (itemHeight := 20) (count := 100)
        (modifier := Modifier.fillMaxWidth) fun i =>
      block 100 20 (if i % 2 == 0 then .red else .green)
  r.settle
  check "lazy pixels: row 0 at the top" (near (← r.pixel 50 10) .red)
  check "lazy pixels: row 1 below" (near (← r.pixel 50 30) .green)
  r.wheel 50 50 (-2)   -- 100 px = 5 rows
  r.settle
  check s!"lazy pixels: wheel moved the window ({← st.value})" ((← st.value) == 100)
  check "lazy pixels: row 5 (odd) now on top" (near (← r.pixel 50 10) .green)
  st.scrollTo (100 * 20 - 100)
  r.settle
  check "lazy pixels: last row (99, odd) at the bottom" (near (← r.pixel 50 90) .green)
  check "lazy pixels: row 95 (odd) at the top" (near (← r.pixel 50 10) .green)
  check "lazy pixels: row 96 (even) below it" (near (← r.pixel 50 30) .red)

/-! ## Popup -/

/-- A dismissable popup gated on `open`, anchored at `anchor`. -/
private def popupContent (open' : MutableState Bool) (anchor : Rect)
    (body : Composable Unit) : Composable Unit :=
  themed <| Box (modifier := Modifier.fillMaxSize |>.background .green)
    (Tests.restartable 1 do
      if ← open'.get then
        withGroup 1 <| Popup body (anchor := some anchor)
          (onDismissRequest := some (open'.set false))
      else
        withGroup 2 (pure ()))

/-- Opens above the main content, positions below its anchor, dismisses on
outside click / Esc but not on inside clicks. -/
private def popupBasics : IO Unit := do
  let open' ← MutableState.create false
  let r ← oboot <| popupContent open' ⟨50, 50, 100, 70⟩
    (Box (modifier := Modifier.size 60 40 |>.background .red))
  check "popup: closed — backdrop everywhere" (near (← r.pixel 60 80) .green)
  open'.set true
  r.settle
  -- Anchored below (50, 70): red 50..110 × 70..110, over the main content.
  check "popup: opens above the main content" (near (← r.pixel 60 80) .red)
  check "popup: positioned below the anchor" (near (← r.pixel 60 65) .green)
  check "popup: sized to its content" (near (← r.pixel 130 80) .green)
  -- Click inside: stays open.
  r.click 60 80
  r.settle
  check "popup: click inside does not dismiss" ((← open'.cell.get) == true)
  check "popup: still drawn" (near (← r.pixel 60 80) .red)
  -- Click outside: dismissed.
  r.click 200 200
  r.settle
  check "popup: click outside dismisses" ((← open'.cell.get) == false)
  check "popup: gone after dismissal" (near (← r.pixel 60 80) .green)
  -- Esc dismisses too.
  open'.set true
  r.settle
  check "popup: reopened" (near (← r.pixel 60 80) .red)
  r.key .escape
  r.settle
  check "popup: Esc dismisses" ((← open'.cell.get) == false)
  check "popup: gone after Esc" (near (← r.pixel 60 80) .green)

/-- An anchor near the bottom flips the popup above itself; positions clamp
to the window. -/
private def popupFlip : IO Unit := do
  let open' ← MutableState.create true
  let r ← oboot <| popupContent open' ⟨50, 250, 100, 290⟩
    (Box (modifier := Modifier.size 60 40 |>.background .red))
  r.settle
  -- No room below (290 + 40 > 300): above the anchor at y 210..250.
  check "popup flip: drawn above the anchor" (near (← r.pixel 60 230) .red)
  check "popup flip: nothing below the anchor" (near (← r.pixel 60 295) .green)
  check "popup flip: anchor row itself is backdrop" (near (← r.pixel 60 270) .green)

/-- Esc dismisses the innermost of two stacked popups first. -/
private def popupStackedEsc : IO Unit := do
  let open1 ← MutableState.create true
  let open2 ← MutableState.create true
  let r ← oboot <| themed <| Box (modifier := Modifier.fillMaxSize |>.background .green) do
    Tests.restartable 1 do
      if ← open1.get then
        withGroup 1 <| Popup (Box (modifier := Modifier.size 60 30 |>.background .red))
          (anchor := some ⟨20, 20, 40, 40⟩)
          (onDismissRequest := some (open1.set false))
      else
        withGroup 2 (pure ())
    Tests.restartable 2 do
      if ← open2.get then
        withGroup 3 <| Popup (Box (modifier := Modifier.size 60 30 |>.background .blue))
          (anchor := some ⟨150, 20, 170, 40⟩)
          (onDismissRequest := some (open2.set false))
      else
        withGroup 4 (pure ())
  r.settle
  check "stacked: both popups drawn"
    (near (← r.pixel 30 50) .red && near (← r.pixel 160 50) .blue)
  r.key .escape
  r.settle
  check "stacked: Esc dismisses the innermost (last opened) first"
    ((← open2.cell.get) == false && (← open1.cell.get) == true)
  check "stacked: outer still drawn" (near (← r.pixel 30 50) .red)
  check "stacked: inner gone" (near (← r.pixel 160 50) .green)
  r.key .escape
  r.settle
  check "stacked: second Esc dismisses the outer" ((← open1.cell.get) == false)

/-! ## Dialog -/

/-- The scrim blocks clicks to a button below it and dims pixels; scrim
click and Esc dismiss; a content click does not. -/
private def dialogModal : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let open' ← MutableState.create false
  let r ← oboot <| themed <| Box (modifier := Modifier.fillMaxSize |>.background .white) do
    Button (clicks.modify (· + 1)) (Text "OK")
    Tests.restartable 1 do
      if ← open'.get then
        withGroup 1 <| Dialog (open'.set false)
          (Box (modifier := Modifier.size 80 40 |>.background .red))
      else
        withGroup 2 (pure ())
  -- Baseline: the button works.
  r.click 30 20
  r.settle
  checkEq "dialog: button clickable before opening" (← clicks.get) 1
  open'.set true
  r.settle
  -- Scrim dims: 32 % black over white ≈ 173.
  let dimmed := overWhite dialogScrimColor
  check s!"dialog: scrim dims the backdrop ({showColor (← r.pixel 250 250)})"
    (near (← r.pixel 250 250) dimmed 6)
  check "dialog: content centered over the scrim" (near (← r.pixel 150 150) .red)
  -- A click at the button's position lands on the scrim: the callback must
  -- NOT fire (the scrim swallows input below; it also requests dismissal —
  -- the dialog's own semantics).
  r.click 30 20
  r.settle
  checkEq "dialog: scrim blocks the button below" (← clicks.get) 1
  check "dialog: scrim click dismisses" ((← open'.cell.get) == false)
  check "dialog: backdrop undimmed after dismissal" (near (← r.pixel 250 250) .white)
  -- Content clicks do not dismiss.
  open'.set true
  r.settle
  r.click 150 150
  r.settle
  check "dialog: content click does not dismiss" ((← open'.cell.get) == true)
  checkEq "dialog: content click does not reach below" (← clicks.get) 1
  -- Wheel over the scrim must not scroll anything below (consumed): just
  -- assert it is delivered nowhere harmful — Esc still dismisses after.
  r.key .escape
  r.settle
  check "dialog: Esc dismisses" ((← open'.cell.get) == false)
  r.click 30 20
  r.settle
  checkEq "dialog: button clickable again after dismissal" (← clicks.get) 2

/-- `blurBehind`: an open dialog wraps the window's *base* content in a blur
layer (radius 8 dp → σ 4 px at density 1), the dialog's own content stays
outside it, and closing removes the layer and resets the state. (Pixels
can't assert this rig — the software renderer documentedly ignores blur —
so the recorded display list is the witness; gpu-probe ⑭ covers the GPU
pixels.) -/
private def dialogBlurBehind : IO Unit := do
  let open' ← MutableState.create true
  let r ← oboot <| themed <| Box (modifier := Modifier.fillMaxSize |>.background .white) do
    Box (modifier := Modifier.size 60 40 |>.background .red)
    Tests.restartable 1 do
      if ← open'.get then
        withGroup 1 <| Dialog (open'.set false) (blurBehind := 8)
          (Box (modifier := Modifier.size 80 40 |>.background .blue))
      else
        withGroup 2 (pure ())
  r.settle
  checkEq "blur-behind: the max radius lands in the window state"
    (← r.ctx.backdropBlurState.cell.get) 8
  let (frame, _) ← Compose.Draw.DrawScope.record {} r.ctx.root.drawTree
  let isBlurLayer : Compose.Draw.Prim → Bool := fun p =>
    match p with
    | .layer _ _ props _ => (props.effect matches .blur _)
    | _ => false
  match frame.find? isBlurLayer with
  | some (.layer _ _ props inner) =>
    let sigma : Float32 := match props.effect with | .blur s => s | _ => 0
    checkEq "blur-behind: σ = radius/2 px" sigma 4
    let innerBriefs := String.intercalate "\n" (inner.map (·.brief)).toList
    check "blur-behind: the base content is inside the blur layer"
      ((innerBriefs.splitOn "#ff0000ff").length ≥ 2)
    check "blur-behind: the dialog content stays outside it"
      ((innerBriefs.splitOn "#0000ffff").length == 1)
  | _ => check "blur-behind: a blur layer wraps the base content" false
  open'.set false
  r.settle
  checkEq "blur-behind: closing resets the state" (← r.ctx.backdropBlurState.cell.get) 0
  let (after, _) ← Compose.Draw.DrawScope.record {} r.ctx.root.drawTree
  check "blur-behind: no blur layer after closing" (after.find? isBlurLayer |>.isNone)

/-- AlertDialog: title/text/buttons render and the confirm button fires. -/
private def alertDialogBasics : IO Unit := do
  let open' ← MutableState.create true
  let confirmed ← IO.mkRef (0 : Nat)
  let r ← oboot <| themed <| Box (modifier := Modifier.fillMaxSize |>.background .white)
    (Tests.restartable 1 do
      if ← open'.get then
        withGroup 1 <| AlertDialog (onDismissRequest := open'.set false)
          (title := "Title") (text := "Body text")
          (confirmButton :=
            TextButton (do confirmed.modify (· + 1); open'.set false) (Text "OK"))
      else
        withGroup 2 (pure ()))
  r.settle
  -- The dialog surface is a centered light card over the dimmed backdrop.
  check "alert: surface drawn in the center" (near (← r.pixel 150 150) L.surface 6)
  check "alert: scrim outside" (near (← r.pixel 20 280) (overWhite dialogScrimColor) 6)
  -- Find the confirm button by probing for primary-colored label pixels is
  -- brittle; click via the surface's bottom-right action row instead.
  let surf ← (← r.ctx.sdlRenderer).readPixels
  let mut hit : Option (Int32 × Int32) := none
  for y in [100:220] do
    for x in [60:260] do
      let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if near c L.primary 30 then
        hit := hit <|> some (Int32.ofNat x, Int32.ofNat y)
  let some (bx, by') := hit
    | do check "alert: confirm label found" false
  r.click bx.toFloat32 by'.toFloat32
  r.settle
  checkEq "alert: confirm button fires" (← confirmed.get) 1
  check "alert: closed by the confirm handler" ((← open'.cell.get) == false)

/-! ## DropdownMenu -/

private structure MenuFixture where
  expanded : MutableState Bool
  selected : MutableState String
  toggles : IO.Ref (Array Bool)

private def menuUi (f : MenuFixture) : Composable Unit :=
  themed <| Box (modifier := Modifier.fillMaxSize |>.background .green)
    (Tests.restartable 1 do
      let isOpen ← f.expanded.get
      ExposedDropdownMenuBox isOpen
        (fun v => do f.toggles.modify (·.push v); f.expanded.set v)
        fun scope => do
          ExposedDropdownMenuField scope (← f.selected.get) (expanded := isOpen)
          let anchor ← scope.anchor
          DropdownMenu isOpen (onDismissRequest := f.expanded.set false)
              (anchor := anchor) (matchAnchorWidth := true) do
            for name in ["Alpha", "Beta", "Gamma"] do
              keyed name <| DropdownMenuItem name
                (onClick := do f.selected.set name; f.expanded.set false))

/-- The combobox toggles open on click; the menu draws over the content;
item click selects and closes. -/
private def menuMouse : IO Unit := do
  let f : MenuFixture :=
    { expanded := ← MutableState.create false
      selected := ← MutableState.create "Alpha"
      toggles := ← IO.mkRef #[] }
  let r ← oboot (menuUi f)
  r.settle
  -- The field is at the top-left (~160×40); below it: backdrop.
  check "menu: field drawn" (near (← r.pixel 80 20) L.surface 6)
  check "menu: backdrop below the field" (near (← r.pixel 80 80) .green)
  r.click 80 20
  r.settle
  checkEq "menu: field click toggles open" (← f.toggles.get) #[true]
  check "menu: expanded" ((← f.expanded.cell.get) == true)
  -- The menu surface now covers the area below the anchor.
  check s!"menu: items drawn over the content ({showColor (← r.pixel 80 80)})"
    (near (← r.pixel 80 80) L.surface 8)
  -- First item ≈ y 51..87 (border 1 + vertical padding 8, item ≥ 36 tall).
  r.click 60 65
  r.settle
  checkEq "menu: item click selects" (← f.selected.cell.get) "Alpha"
  check "menu: item click closes (caller-driven)" ((← f.expanded.cell.get) == false)
  check "menu: closed menu leaves the backdrop" (near (← r.pixel 80 80) .green)
  -- Outside click dismisses without selecting.
  r.click 80 20
  r.settle
  check "menu: reopened" ((← f.expanded.cell.get) == true)
  r.click 250 250
  r.settle
  check "menu: outside click dismisses" ((← f.expanded.cell.get) == false)
  checkEq "menu: outside click selects nothing" (← f.selected.cell.get) "Alpha"

/-- Keyboard: Down/Down/Enter activates the second item while the popup
grabs key routing (the focused anchor's Enter handling must not fire). -/
private def menuKeyboard : IO Unit := do
  let f : MenuFixture :=
    { expanded := ← MutableState.create false
      selected := ← MutableState.create "Alpha"
      toggles := ← IO.mkRef #[] }
  let r ← oboot (menuUi f)
  r.settle
  r.click 80 20
  r.settle
  check "menu keys: open (field focused)" ((← f.expanded.cell.get) == true)
  r.key .down
  r.key .down
  r.settle
  r.key .return
  r.settle
  checkEq "menu keys: Down/Down/Enter selects the second item"
    (← f.selected.cell.get) "Beta"
  check "menu keys: selection closed the menu" ((← f.expanded.cell.get) == false)
  checkEq "menu keys: the focused anchor did not re-toggle"
    (← f.toggles.get) #[true]
  -- Esc closes an opened menu without selecting.
  r.click 80 20
  r.settle
  r.key .escape
  r.settle
  check "menu keys: Esc dismisses" ((← f.expanded.cell.get) == false)
  checkEq "menu keys: Esc selects nothing" (← f.selected.cell.get) "Beta"

/-- A dropdown kept mounted only to play its exit animation is *inert*: while
closing (mounted but no longer `expanded`) it neither dismiss-catches clicks
nor grabs keys, and its whole layer is transparent to hit-testing — so input
aimed elsewhere is not swallowed by the dying menu. Re-opening mid-exit
restores interactivity. The exit window is driven by frame ticks (`s`), so
`render`/`runDue` progress input without unmounting the menu. -/
private def menuExitInert : IO Unit := do
  let expanded ← MutableState.create false
  let btn ← IO.mkRef (0 : Nat)
  let keyHits ← IO.mkRef (0 : Nat)
  let r ← oboot <| themed <| Column (modifier := Modifier.fillMaxSize |>.background .white) do
    Spacer (Modifier.size 100 200)
    Spacer (Modifier.size 80 40 |>.background .blue |>.clickable (btn.modify (· + 1)))
    Tests.restartable 1 do
      DropdownMenu (← expanded.get) (onDismissRequest := expanded.set false)
          (anchor := some ⟨10, 10, 60, 30⟩) do
        DropdownMenuItem "Pick" (onClick := expanded.set false)
  -- A normal (non-capture) app key handler standing in for "the rest of the
  -- app": an inert menu must let keys reach it.
  let hid ← freshId
  r.ctx.registerKeyHandler
    { id := hid, capture := false
      handler := fun ke => do
        if ke.down && ke.key == .down then keyHits.modify (· + 1)
        return false }
  r.settle
  -- Baseline: with no menu open, the button at (40, 220) is clickable.
  r.click 40 220
  r.s.runDue (← r.clock.get)
  checkEq "exit: button clickable at baseline" (← btn.get) 1
  btn.set 0
  -- Open and let the enter transition finish.
  expanded.set true
  r.settle
  check "exit: menu open" ((← expanded.cell.get) == true)
  -- Begin closing (caller-driven — an item pick / onDismissRequest), then start
  -- but do NOT finish the exit animation: the menu is now mounted yet inert.
  expanded.set false
  r.render
  r.s.runDue (← r.clock.get)
  r.render
  -- 1) A click on the button below reaches it — the dying menu's (pre-fix
  --    full-window) dismiss scrim no longer intercepts.
  r.click 40 220
  r.s.runDue (← r.clock.get)
  r.render
  checkEq "exit: click during exit reaches the button below" (← btn.get) 1
  -- 2) A key during exit reaches the normal app handler, not the dead menu
  --    (pre-fix the menu's capture handler consumes Down).
  r.key .down
  r.s.runDue (← r.clock.get)
  checkEq "exit: key during exit reaches normal handlers" (← keyHits.get) 1
  -- 3) Re-opening mid-exit restores interactivity: the dismiss scrim is back, so
  --    an off-menu click is swallowed (requesting dismissal) and does not reach
  --    the button below.
  btn.set 0
  expanded.set true
  r.render
  r.s.runDue (← r.clock.get)
  r.render
  r.click 40 220
  r.s.runDue (← r.clock.get)
  r.render
  checkEq "exit: re-open restores the scrim (button below blocked)" (← btn.get) 0
  check "exit: re-open scrim dismiss fired" ((← expanded.cell.get) == false)
  r.settle

/-- The overlay group. -/
def run : IO Unit := do
  scrollWheel
  scrollProgrammatic
  scrollNested
  scrollbarGeometry
  scrollbarDrag
  scrollbarAutoHide
  lazyVirtualization
  lazyStateSwap
  lazyWheelPixels
  popupBasics
  popupFlip
  popupStackedEsc
  dialogModal
  dialogBlurBehind
  alertDialogBasics
  menuMouse
  menuKeyboard
  menuExitInert

end Tests.Overlay
