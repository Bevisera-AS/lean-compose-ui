import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# TextField test group (`test/ComposeTests/TextField.lean`)

M11's end-to-end editing suites, headless. The value-flow suites (typing,
editing scripts, UTF-8, `TextField`) are written in the MT framework
(`Compose.Test`): `runComposeTest` + `typeText`/`pressKey` through the real
input path, with `checkEq` on the controlled state for selection-precise
expectations. The pixel/geometry suites (mouse selection, clipboard, caret
blink, IME, auto-scroll, outline states) keep the raw `TRig` — pixel output
is the property under test there, and glyph-coordinate expectations come
from a probe `TextLayout` sharing the window's font stack.

The caret-blink `InfiniteTransition` keeps frame work alive while a field is
focused, so the TRig tests advance time with bounded `pump`s instead of
settle-until-idle.
-/

namespace Tests.TextField
open Compose Compose.Test Tests.Harness

/-- Test config: software renderer for stable `readPixels`, no vsync. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

private def L : ColorScheme := .light

/-- Whether an SDL pixel is within `tol` byte-steps of a theme color. -/
private def near (c : Sdl.Color) (e : Compose.Color) (tol : Nat := 6) : Bool :=
  let (r, g, b, _) := e.toBytes
  colorNear c r g b tol

private def vstr (v : TextFieldValue) : String :=
  s!"'{v.text}'@{v.selection.anchor}-{v.selection.active}"
    ++ match v.composition with
       | some c => s!" comp[{c.anchor},{c.active}]"
       | none => ""

private instance : ToString TextFieldValue := ⟨vstr⟩

/-! ## Rig -/

private structure TRig where
  ctx : WindowContext
  s : Scheduler
  clock : IO.Ref UInt64

/-- Bootstrap `content` under a fake-clock `LocalScheduler` inside the theme,
start the queued coroutines, render the first frame. -/
private def tboot (content : Composable Unit) (w : Dp := 240) (h : Dp := 160) :
    IO TRig := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  let ctx ← bootstrap "compose-textfield-test" w h
    (CompositionLocalProvider LocalScheduler (some s)
      (MaterialTheme content)) cfg
  let _ ← step ctx cfg
  s.runDue 0
  return { ctx, s, clock }

private def TRig.render (r : TRig) : IO Unit := do
  if ← r.ctx.needsFrame.get then
    let _ ← step r.ctx cfg

/-- Advance the fake clock by `dtMs`, run coroutines + frame clock, render. -/
private def TRig.tick (r : TRig) (dtMs : UInt64) : IO Unit := do
  let t := (← r.clock.get) + dtMs * 1_000_000
  r.clock.set t
  r.s.runDue t
  r.s.tickFrame t
  r.render

/-- Recompose/redraw and run a few short animation frames (blink-friendly:
advances little time). -/
private def TRig.pump (r : TRig) : IO Unit := do
  r.render
  r.s.runDue (← r.clock.get)
  for _ in [0:3] do r.tick 8

private def TRig.pixel (r : TRig) (x y : Int32) : IO Sdl.Color := do
  (← (← r.ctx.sdlRenderer).readPixels).readPixel x y

private def TRig.send (r : TRig) (e : Sdl.Event) : IO Unit :=
  dispatchEvent r.ctx cfg e

private def TRig.press (r : TRig) (x y : Float32) (clicks : UInt8 := 1) : IO Unit :=
  r.send (.mouseButtonDown ⟨0, ⟨0⟩, ⟨0⟩, .left, true, clicks, x, y⟩)

private def TRig.release (r : TRig) (x y : Float32) (clicks : UInt8 := 1) : IO Unit :=
  r.send (.mouseButtonUp ⟨0, ⟨0⟩, ⟨0⟩, .left, false, clicks, x, y⟩)

private def TRig.click (r : TRig) (x y : Float32) (clicks : UInt8 := 1) : IO Unit := do
  r.press x y clicks
  r.release x y clicks

private def TRig.move (r : TRig) (x y : Float32) : IO Unit :=
  r.send (.mouseMotion ⟨0, ⟨0⟩, ⟨0⟩, .none, x, y, 0, 0⟩)

/-! Finger events (normalized coordinates over the 240×160 test window;
translated to pointer id `fingerId + 1` — the touch pointer pipeline). -/

private def TRig.fingerDown (r : TRig) (x y : Float32) : IO Unit :=
  r.send (.fingerDown ⟨0, ⟨1⟩, ⟨0⟩, x / 240, y / 160, 0, 0, 1, ⟨0⟩⟩)

private def TRig.fingerMove (r : TRig) (x y : Float32) : IO Unit :=
  r.send (.fingerMotion ⟨0, ⟨1⟩, ⟨0⟩, x / 240, y / 160, 0, 0, 1, ⟨0⟩⟩)

private def TRig.fingerUp (r : TRig) (x y : Float32) : IO Unit :=
  r.send (.fingerUp ⟨0, ⟨1⟩, ⟨0⟩, x / 240, y / 160, 0, 0, 1, ⟨0⟩⟩)

private def TRig.key (r : TRig) (k : Sdl.Keycode) (mods : Sdl.Keymod := .none) : IO Unit :=
  r.send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, k, mods, 0, true, false⟩)

private def TRig.text (r : TRig) (t : String) : IO Unit :=
  r.send (.textInput ⟨0, ⟨0⟩, t⟩)

private def TRig.editing (r : TRig) (t : String) (start length : Int32) : IO Unit :=
  r.send (.textEditing ⟨0, ⟨0⟩, t, start, length⟩)

/-- The field's effective text style under the theme (bodyMedium 14 sp,
20 sp line height) — for probe layouts computing glyph geometry. -/
private def probeStyle : TextStyle := { fontSize := 14, lineHeight := some 20 }

/-- A probe layout over the window's font stack (glyph x-coordinates). -/
private def probeLayout (r : TRig) (text : String) : IO TextLayout := do
  let l ← TextLayout.create r.ctx.textContext.textEngine r.ctx.textContext.fontStore
    text probeStyle {}
  let _ ← l.measure none
  return l

/-- Screen x of the caret slot before byte `off` in the field's text (field
at the window origin, 12 px content padding, scroll 0). -/
private def caretScreenX (r : TRig) (text : String) (off : Nat) : IO Float32 := do
  let l ← probeLayout r text
  if off ≥ text.utf8ByteSize then
    return 12 + (← l.measure none).width.toFloat32
  return 12 + (← l.byteOffsetToRect off).left

/-- Boot a controlled `ValueTextField` bound to fresh state; returns the rig, the
state, and the change log. -/
private def fieldRig (initial : TextFieldValue := {}) (w : Dp := 240)
    (placeholder : String := "") (label : Option String := none)
    (isError : Bool := false) (enabled : Bool := true) (fieldWidth : Option Dp := none) :
    IO (TRig × MutableState TextFieldValue × IO.Ref (Array TextFieldValue)) := do
  let value ← MutableState.create initial
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  let m := match fieldWidth with
    | some fw => Modifier.width fw
    | none => {}
  let r ← tboot (w := w) <| Tests.restartable 1 do
    let v ← value.get
    ValueTextField v (fun v' => do calls.modify (·.push v'); value.set v')
      (modifier := m) (enabled := enabled) (isError := isError)
      (placeholder := placeholder) (label := label)
  return (r, value, calls)

/-- Android touch on a field inside a scrollable: a finger flick starting
on the field belongs to the scroll container (moves pass through
unconsumed, the drag-scroll steals past slop, the field neither edits nor
places a caret — and the router's tap-gated focus never fires, so no
keyboard pop); a finger *tap* places the caret at the release. -/
private def touchFieldGesture : IO Unit := do
  let text := "hello world"
  let value ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  let st ← ScrollState.create
  let r ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st) do
      Column do
        let v ← value.get
        ValueTextField v (fun v' => do calls.modify (·.push v'); value.set v')
        Box (modifier := Modifier.size 240 300) do pure ()
  -- A tap places the caret at the release (byte boundary 3, like the
  -- mouse click).
  let x3 ← caretScreenX r text 3
  r.fingerDown (x3 + 1) 20
  r.fingerUp (x3 + 1) 20
  r.pump
  checkEq "touch field: a tap places the caret at the up" (← value.get)
    (⟨text, .caret 3, none⟩)
  -- Flick up starting on the field (y 30 is inside the ~40 dp field box):
  -- the scroll steals past slop and the content scrolls.
  r.fingerDown 100 30
  r.fingerMove 100 16
  r.fingerMove 100 2
  r.fingerUp 100 2
  r.pump
  check s!"touch field: the flick scrolls the container ({← st.value})"
    ((← st.value) > 10)
  checkEq "touch field: the flick never edits or moves the caret"
    ((← calls.get).size) 1
  -- The field's gesture handler survives the steal: a tap after the flick
  -- (y corrected for the scrolled content) still places a caret.
  let x8 ← caretScreenX r text 8
  r.fingerDown (x8 + 1) (20 - (← st.value))
  r.fingerUp (x8 + 1) (20 - (← st.value))
  r.pump
  checkEq "touch field: a tap after the flick still works" (← value.get)
    (⟨text, .caret 8, none⟩)

/-- Android long-press selection on touch: holding the finger past the
long-press timeout selects the word under it; dragging then extends the
selection word-anchored with moves *consumed* (the enclosing scroll stands
off — the field owns the pointer). A flick that crosses the scroll slop
before the timeout still scrolls, and the raced-out timer must not fire
late. -/
private def touchLongPress : IO Unit := do
  let text := "hello world"
  let value ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let st ← ScrollState.create
  let r ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st) do
      Column do
        let v ← value.get
        ValueTextField v value.set
        Box (modifier := Modifier.size 240 300) do pure ()
  -- Long-press inside "hello" (no release): the timer selects the word.
  let x2 ← caretScreenX r text 2
  r.fingerDown (x2 + 1) 20
  r.tick 600
  checkEq "long-press: selects the word under the finger" (← value.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  -- Drag forward past the word: extends word-start → caret, and the
  -- consumed moves keep the scroll parked.
  let x8 ← caretScreenX r text 8
  r.fingerMove (x8 + 1) 20
  checkEq "long-press: drag extends word-anchored" (← value.get)
    (⟨text, ⟨0, 8⟩, none⟩)
  r.fingerMove (x8 + 1) 60
  checkEq "long-press: selection drag never scrolls" (← st.value) 0
  -- Release keeps the selection.
  r.fingerUp (x8 + 1) 60
  r.pump
  checkEq "long-press: release keeps the selection" ((← value.get).selection.«end») 8
  checkEq "long-press: still no scroll after the up" (← st.value) 0
  -- Drag back before the word start from a fresh long-press on "world":
  -- anchors at the word end.
  let x7 ← caretScreenX r text 7
  r.fingerDown (x7 + 1) 20
  r.tick 600
  checkEq "long-press: second press selects its word" (← value.get)
    (⟨text, ⟨6, 11⟩, none⟩)
  let x2b ← caretScreenX r text 2
  r.fingerMove (x2b + 1) 20
  checkEq "long-press: backward drag anchors at the word end" (← value.get)
    (⟨text, ⟨11, 2⟩, none⟩)
  r.fingerUp (x2b + 1) 20
  r.pump
  -- Dismiss the selection chrome first (a tap collapses the selection and
  -- hides the handles) — the flick below starts where the end handle's
  -- touch box would otherwise sit, and flicking a handle drags it.
  let x7b ← caretScreenX r text 7
  r.fingerDown (x7b + 1) 20
  r.fingerUp (x7b + 1) 20
  r.pump
  -- A flick that crosses slop before the timeout scrolls and cancels the
  -- pending long-press: the raced-out timer must not select late.
  let before ← value.get
  r.fingerDown 100 30
  r.fingerMove 100 16
  r.fingerMove 100 2
  r.fingerUp 100 2
  r.pump
  check s!"long-press: pre-timeout flick scrolls ({← st.value})" ((← st.value) > 10)
  r.tick 600
  checkEq "long-press: the raced-out timer never fires" (← value.get) before

/-- Touch selection chrome, handles half: a finger long-press raises the
floating handles once the finger settles (mouse selection never does);
dragging a handle moves the selection with character granularity (not
word-anchored), the grabbed end crossing the fixed end swaps roles, an
enclosing scroll never steals the drag (the handle popup consumes from
the press), the field keeps focus through handle interaction
(`Modifier.focusNeutral`), and a caret tap dismisses the chrome.

Geometry (density 1, field at the origin): text line spans y 10–30, so
handle touch boxes hang at y 30–62 with the teardrop circle centered
12 px below the line (y 42). The end handle's tip is its box's top-left
corner (circle center x = anchor + 12); the start handle's box is
left-of-anchor and window-clamped at the left edge, putting its circle
center at x 20 for a selection starting at offset 0. -/
private def touchSelectionHandles : IO Unit := do
  let text := "hello world"
  let value ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let st ← ScrollState.create
  let r ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st) do
      Column do
        let v ← value.get
        ValueTextField v value.set
        Box (modifier := Modifier.size 240 300) do pure ()
  -- Long-press "hello", release: handles appear at both selection ends.
  let x2 ← caretScreenX r text 2
  r.fingerDown (x2 + 1) 20
  r.tick 600
  r.fingerUp (x2 + 1) 20
  r.pump
  r.pump
  let x5 ← caretScreenX r text 5
  check "handles: end handle at the selection end"
    (near (← r.pixel (x5 + 12).toInt32 42) L.primary)
  check "handles: start handle at the selection start (edge-clamped box)"
    (near (← r.pixel 20 42) L.primary)
  -- Drag the end handle back inside the word: character granularity (the
  -- word-anchored selDrag would keep (0, 5)); y is ignored and the
  -- consumed drag keeps the enclosing scroll parked.
  let x3 ← caretScreenX r text 3
  r.fingerDown (x5 + 12) 42
  r.fingerMove (x3 + 1) 42
  checkEq "handles: end-handle drag is char-granular" (← value.get)
    (⟨text, ⟨0, 3⟩, none⟩)
  r.fingerMove (x3 + 1) 100
  checkEq "handles: handle drag never scrolls" (← st.value) 0
  r.fingerUp (x3 + 1) 100
  r.pump
  r.pump
  -- Chrome survives the handle interaction (focus-neutral press): the end
  -- handle now sits at the new selection end.
  check "handles: chrome tracks the selection after the drag"
    (near (← r.pixel (x3 + 12).toInt32 42) L.primary)
  -- Crossing: select "world", grab its END handle, drag left past the
  -- start (roles swap to the start handle), then right past the fixed end
  -- (they swap back).
  let x7 ← caretScreenX r text 7
  r.fingerDown (x7 + 1) 20
  r.fingerUp (x7 + 1) 20
  r.pump
  r.fingerDown (x7 + 1) 20
  r.tick 600
  r.fingerUp (x7 + 1) 20
  r.pump
  r.pump
  checkEq "handles: long-press selects the second word" (← value.get)
    (⟨text, ⟨6, 11⟩, none⟩)
  let x11 ← caretScreenX r text 11
  let x8 ← caretScreenX r text 8
  r.fingerDown (x11 + 12) 42
  r.fingerMove (x3 + 1) 42
  checkEq "handles: crossing the fixed end swaps the grabbed role"
    (← value.get) (⟨text, ⟨6, 3⟩, none⟩)
  r.fingerMove (x8 + 1) 42
  checkEq "handles: crossing back swaps again" (← value.get)
    (⟨text, ⟨6, 8⟩, none⟩)
  r.fingerUp (x8 + 1) 42
  r.pump
  -- A caret tap collapses the selection and dismisses the chrome.
  r.fingerDown (x2 + 1) 20
  r.fingerUp (x2 + 1) 20
  r.pump
  r.pump
  checkEq "handles: a tap collapses the selection" (← value.get)
    (⟨text, .caret 2, none⟩)
  check "handles: the tap dismissed the chrome"
    (!near (← r.pixel 20 42) L.primary)
  -- Mouse selection never raises chrome (touch-only invariant).
  r.click (x2 + 1) 20 (clicks := 2)
  r.pump
  r.pump
  checkEq "handles: mouse double-click still selects" (← value.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  check "handles: no chrome for mouse selection"
    (!near (← r.pixel (x5 + 12).toInt32 42) L.primary
     && !near (← r.pixel 20 42) L.primary)

/-- Touch selection chrome, edges: scrolling the enclosing container under
shown chrome moves the handles WITH the text (Android's native behavior —
the toolbar sits the motion out and returns, repositioned, when it
settles); a selection scrolled fully out of the viewport suppresses the
chrome instead of leaving it floating over neighboring content; and
dragging a handle past a narrow field's edge rides the caret auto-scroll
(the dragged end is `active`), extending the selection beyond the visible
window while the scrolled-out start handle is suppressed. -/
private def touchChromeEdges : IO Unit := do
  let text := "hello world"
  let value ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let st ← ScrollState.create
  let r ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st) do
      Column do
        let v ← value.get
        ValueTextField v value.set
        Box (modifier := Modifier.size 240 300) do pure ()
  -- Select "hello", settle: chrome up.
  let x2 ← caretScreenX r text 2
  let x5 ← caretScreenX r text 5
  r.fingerDown (x2 + 1) 20
  r.tick 600
  r.fingerUp (x2 + 1) 20
  r.pump
  r.pump
  check "chrome edges: chrome up before the scroll"
    (near (← r.pixel (x5 + 12).toInt32 42) L.primary)
  -- Finger-scroll the container from the filler below the field (x 220:
  -- clear of the toolbar at y 70–110 and the handles): the handles track
  -- the moving text, the selection persists, and the settled toolbar
  -- returns at its shifted position (Copy there proves both).
  Sdl.setClipboardText "reset"
  r.fingerDown 220 80
  r.fingerMove 220 66
  r.fingerMove 220 52
  r.fingerUp 220 52
  r.tick 600
  r.pump
  let sv ← st.value
  check s!"chrome edges: the container scrolled ({sv})" (sv > 10)
  checkEq "chrome edges: the selection persists" (← value.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  check "chrome edges: the handles track the scrolled field"
    (near (← r.pixel (x5 + 12).toInt32 (42 - sv).toInt32) L.primary)
  r.fingerDown 108 (90 - sv)
  r.fingerUp 108 (90 - sv)
  r.pump
  checkEq "chrome edges: the settled toolbar works at its shifted position"
    (← Sdl.getClipboardText) "hello"
  -- Scrolled fully out of the viewport: chrome is suppressed, not left
  -- floating (or edge-clamped) over the neighboring content.
  let value3 ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let st3 ← ScrollState.create
  let r3 ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st3) do
      Column do
        let v ← value3.get
        ValueTextField v value3.set
        Box (modifier := Modifier.size 240 300) do pure ()
  r3.fingerDown (x2 + 1) 20
  r3.tick 600
  r3.fingerUp (x2 + 1) 20
  r3.pump
  r3.pump
  for _ in [0:2] do
    r3.fingerDown 220 90
    r3.fingerMove 220 60
    r3.fingerMove 220 30
    r3.fingerMove 220 5
    r3.fingerUp 220 5
    r3.tick 700
  r3.pump
  check s!"premise: scrolled past the field ({← st3.value})" ((← st3.value) > 72)
  checkEq "chrome edges: the off-viewport selection persists" (← value3.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  check "chrome edges: off-viewport chrome is suppressed"
    (!near (← r3.pixel (x5 + 12).toInt32 12) L.primary
     && !near (← r3.pixel 20 12) L.primary)
  -- Narrow field: dragging the end handle past the field edge auto-scrolls
  -- the text under the selection (the dragged end is the caret) and the
  -- start handle, scrolled out of the clip window, is suppressed.
  let (r2, value2, _) ← fieldRig { text, selection := .caret 0 } (fieldWidth := some 80)
  r2.fingerDown (x2 + 1) 20
  r2.tick 600
  r2.fingerUp (x2 + 1) 20
  r2.pump
  r2.pump
  checkEq "chrome edges: narrow-field long-press selects" (← value2.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  r2.fingerDown (x5 + 12) 42
  r2.fingerMove 200 42
  r2.fingerUp 200 42
  r2.pump
  r2.pump
  checkEq "chrome edges: edge drag extends to the text end via auto-scroll"
    (← value2.get) (⟨text, ⟨0, 11⟩, none⟩)
  -- innerW = 80 − 24 = 56: the end handle sits pinned near the clip's
  -- right edge (12 + 56 − caretW + 12 ≈ 78) and the start handle is gone.
  check "chrome edges: the end handle pins to the field edge"
    (near (← r2.pixel 78 42) L.primary)
  check "chrome edges: the scrolled-out start handle is suppressed"
    (!near (← r2.pixel 20 42) L.primary)

/-- Touch selection chrome, toolbar half: the settling finger raises the
Cut/Copy/Paste toolbar over the selection — *below* it when the field sits
at the window top (the `preferAbove` fallback), above it otherwise (proved
by tapping buttons at the resolver-predicted coordinates: the action only
fires if the toolbar is really there). Paste replaces the selection, Copy
copies and collapses to the selection end (deselect-after-copy), Cut
removes the selected text; every action dismisses the chrome; Paste is
present only while the clipboard has text.

Toolbar geometry (density 1): content = fixed 64×40 buttons in Cut, Copy,
Paste order (192 px wide with Paste, 128 without); popup x = the visible
selection start (12 px for a selection at offset 0), y = line bottom + 8
when falling back below (top-rig: 30 + 8 = 38, button centers y 58), or
line top − 40 − 8 when above (spacer rig: 90 − 48 = 42, centers y 62). -/
private def touchSelectionToolbar : IO Unit := do
  let text := "hello world"
  let value ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let st ← ScrollState.create
  let r ← tboot <| Tests.restartable 1 do
    Box (modifier := Modifier.size 240 100 |>.verticalScroll st) do
      Column do
        let v ← value.get
        ValueTextField v value.set
        Box (modifier := Modifier.size 240 300) do pure ()
  Sdl.setClipboardText "XY"
  -- Long-press "hello", settle: toolbar falls back below the line (no room
  -- above), x at the selection start (12).
  let x2 ← caretScreenX r text 2
  r.fingerDown (x2 + 1) 20
  r.tick 600
  r.fingerUp (x2 + 1) 20
  r.pump
  r.pump
  -- Paste replaces the selection and dismisses the chrome.
  r.fingerDown 172 90
  r.fingerUp 172 90
  r.pump
  checkEq "toolbar: Paste replaces the selection" (← value.get)
    (⟨"XY world", .caret 2, none⟩)
  -- Copy: fresh selection on "world", tap Copy at its slot.
  let x5b ← caretScreenX r "XY world" 5
  r.fingerDown (x5b + 1) 20
  r.tick 600
  r.fingerUp (x5b + 1) 20
  r.pump
  r.pump
  checkEq "toolbar: long-press selects the word" (← value.get)
    (⟨"XY world", ⟨3, 8⟩, none⟩)
  let x3b ← caretScreenX r "XY world" 3
  check "premise: toolbar x unclamped" (x3b ≤ 48)
  -- Pressing a button but releasing off it fires nothing and keeps chrome.
  let x8b ← caretScreenX r "XY world" 8
  r.fingerDown (x3b + 96) 90
  r.fingerMove (x3b + 96) 130
  r.fingerUp (x3b + 96) 130
  r.pump
  r.pump
  checkEq "toolbar: a drag-off release fires nothing" (← value.get)
    (⟨"XY world", ⟨3, 8⟩, none⟩)
  check "toolbar: a drag-off release keeps the chrome"
    (near (← r.pixel (x8b + 12).toInt32 42) L.primary)
  r.fingerDown (x3b + 96) 90
  r.fingerUp (x3b + 96) 90
  r.pump
  checkEq "toolbar: Copy fills the clipboard" (← Sdl.getClipboardText) "world"
  checkEq "toolbar: Copy collapses to the selection end (chrome hides)"
    (← value.get) (⟨"XY world", .caret 8, none⟩)
  -- Cut: fresh selection again, tap Cut.
  r.fingerDown (x5b + 1) 20
  r.tick 600
  r.fingerUp (x5b + 1) 20
  r.pump
  r.pump
  r.fingerDown (x3b + 32) 90
  r.fingerUp (x3b + 32) 90
  r.pump
  checkEq "toolbar: Cut removes the selected text" (← value.get)
    (⟨"XY ", .caret 3, none⟩)
  checkEq "toolbar: Cut recopied the selection" (← Sdl.getClipboardText) "world"
  -- Empty clipboard: no Paste button — a tap at its slot misses the
  -- narrower toolbar and lands outside (clearing focus, hiding chrome,
  -- editing nothing).
  Sdl.setClipboardText ""
  check "premise: the clipboard reads empty" (!(← Sdl.hasClipboardText))
  let x1c ← caretScreenX r "XY " 1
  r.fingerDown (x1c + 1) 20
  r.tick 600
  r.fingerUp (x1c + 1) 20
  r.pump
  r.pump
  checkEq "toolbar: long-press selects with an empty clipboard"
    (← value.get) (⟨"XY ", ⟨0, 2⟩, none⟩)
  r.fingerDown 172 90
  r.fingerUp 172 90
  r.pump
  r.pump
  checkEq "toolbar: no Paste button when the clipboard is empty"
    (← value.get) (⟨"XY ", ⟨0, 2⟩, none⟩)
  check "toolbar: the outside tap dismissed the chrome"
    (!near (← r.pixel 20 42) L.primary)
  -- Above-preference: with room over the field (80 px spacer) the toolbar
  -- sits above the selection line — Copy only works at the *above* slot.
  let value2 ← MutableState.create ({ text, selection := .caret 0 } : TextFieldValue)
  let r2 ← tboot <| Tests.restartable 1 do
    Column do
      Box (modifier := Modifier.size 240 80) do pure ()
      let v ← value2.get
      ValueTextField v value2.set
  Sdl.setClipboardText "Z"
  let y2 := 100
  r2.fingerDown (x2 + 1) y2
  r2.tick 600
  r2.fingerUp (x2 + 1) y2
  r2.pump
  r2.pump
  checkEq "toolbar: spacer-rig long-press selects" (← value2.get)
    (⟨text, ⟨0, 5⟩, none⟩)
  r2.fingerDown 108 62
  r2.fingerUp 108 62
  r2.pump
  checkEq "toolbar: prefers the space above the selection"
    (← Sdl.getClipboardText) "hello"
  checkEq "toolbar: deselect-after-copy in the above position"
    (← value2.get) (⟨text, .caret 5, none⟩)

/-- The app→IME sync hook: a focused field pushes its (text, selection) pair
— selection in UTF-16 code units — through `WindowContext.imeSyncHook`
exactly once per change (caret taps and edits alike); an unfocused field
never fires it. -/
private def imeSyncHook : IO Unit := do
  let text := "héllo wörld"   -- multi-byte: the byte→UTF-16 conversion shows
  let (r, value, _) ← fieldRig { text, selection := .caret 0 }
  let syncs ← IO.mkRef (#[] : Array (String × UInt32 × UInt32))
  r.ctx.imeSyncHook.set (some ⟨fun t s e => syncs.modify (·.push (t, s, e))⟩)
  r.pump
  checkEq "ime sync: nothing while unfocused" ((← syncs.get).size) 0
  -- Click after "w" (byte 8 = 7 UTF-16 units: é and ö are 2 bytes, 1 unit).
  let x8 ← caretScreenX r text 8
  r.click (x8 + 1) 20
  r.pump
  checkEq "ime sync: focus click pushed the caret once" (← syncs.get)
    #[(text, 7, 7)]
  r.pump
  checkEq "ime sync: redraws don't re-push" ((← syncs.get).size) 1
  -- Typing changes text + caret: one more push with the new pair.
  r.text "x"
  r.pump
  checkEq "ime sync: an edit pushes the new state" ((← syncs.get).back?)
    (some ("héllo wxörld", 8, 8))
  checkEq "ime sync: exactly one push per change" ((← syncs.get).size) 2
  -- Programmatic selection change while unfocused stays silent.
  r.key .escape
  r.pump
  value.set { (← value.get) with selection := .caret 0 }
  r.pump
  checkEq "ime sync: unfocused programmatic move stays silent"
    ((← syncs.get).size) 2

/-! ## End-to-end typing (controlled loop, MT framework) -/

/-- One tagged controlled `ValueTextField` bound to `value`, logging every
`onValueChange` into `calls` — the content of the MT-framework suites. -/
private def fieldContent (value : MutableState TextFieldValue)
    (calls : IO.Ref (Array TextFieldValue)) : Composable Unit :=
  Tests.restartable 1 do
    let v ← value.get
    ValueTextField v (fun v' => do calls.modify (·.push v'); value.set v')
      (modifier := Modifier.testTag "field")

private def typingEndToEnd : IO Unit := do
  let value ← MutableState.create ({} : TextFieldValue)
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  runComposeTest (fieldContent value calls) do
    -- typeText click-focuses through the real click-to-focus path, then
    -- commits one text event per codepoint.
    typeText (.tag "field") "hi"
    check "typing: focus started the IME session"
      (← (← uiTest).ctx.window.textInputActive)
    assertFocused (.tag "field")
    checkEq "typing: controlled callbacks saw h → hi"
      ((← calls.get).map (·.text)) #["h", "hi"]
    checkEq "typing: caret advanced with each commit"
      ((← calls.get).map (·.selection.active)) #[1, 2]
    assertTextEquals (.tag "field") "hi"
    checkEq "typing: state settled at 'hi'" (← value.get) (⟨"hi", .caret 2, none⟩)
    -- Back-to-back events without a recomposition in between still compose
    -- (the optimistic latest-value ref): raw events, one awaitIdle at the end.
    textInput "!"
    textInput "?"
    awaitIdle
    checkEq "typing: consecutive events compose without recomposition"
      (← value.get) (⟨"hi!?", .caret 4, none⟩)

/-! ## Full keyboard editing scripts (MT framework) -/

private def editingScripts : IO Unit := do
  let value ← MutableState.create ({} : TextFieldValue)
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  runComposeTest (fieldContent value calls) do
    typeText (.tag "field") "hello world"
    checkEq "script: typed the base text" (← value.get)
      (⟨"hello world", .caret 11, none⟩)
    pressKey .left (mods := .lCtrl)                  -- word-left
    checkEq "script: ctrl-Left jumps to the word start" (← value.get)
      (⟨"hello world", .caret 6, none⟩)
    pressKey .«end» (mods := .lShift)                -- shift-End
    checkEq "script: shift-End extends to the end" (← value.get)
      (⟨"hello world", ⟨6, 11⟩, none⟩)
    pressKey .backspace                              -- delete the selection
    checkEq "script: backspace deletes the selection" (← value.get)
      (⟨"hello ", .caret 6, none⟩)
    typeText (.tag "field") "there"
    checkEq "script: typing at the caret inserts" (← value.get)
      (⟨"hello there", .caret 11, none⟩)
    pressKey .home
    checkEq "script: Home to the start" (← value.get)
      (⟨"hello there", .caret 0, none⟩)
    pressKey .right (mods := .lShift)
    pressKey .right (mods := .lShift)
    checkEq "script: two shift-Rights select 'he'" (← value.get)
      (⟨"hello there", ⟨0, 2⟩, none⟩)
    pressKey .right                                  -- collapse to the end
    checkEq "script: plain Right collapses to the selection end" (← value.get)
      (⟨"hello there", .caret 2, none⟩)
    pressKey .right (mods := .lCtrl)                 -- ctrl word-right
    checkEq "script: ctrl-Right word-jumps" (← value.get)
      (⟨"hello there", .caret 5, none⟩)
    pressKey .backspace (mods := .lCtrl)             -- delete word back
    checkEq "script: ctrl-Backspace deletes back to the word start" (← value.get)
      (⟨" there", .caret 0, none⟩)
    pressKey .a (mods := .lCtrl)                     -- select all
    checkEq "script: ctrl-A selects everything" (← value.get)
      (⟨" there", ⟨0, 6⟩, none⟩)
    typeText (.tag "field") "x"                      -- typing replaces selection
    checkEq "script: typing replaces the selection" (← value.get)
      (⟨"x", .caret 1, none⟩)
    pressKey .delete                                 -- deleteForward at the end
    checkEq "script: Delete at the end is a no-op" (← value.get)
      (⟨"x", .caret 1, none⟩)
    -- Tab falls through to traversal (nothing else focusable → wraps back to
    -- the field; the live IME session shows the field is focused again).
    pressKey .tab
    check "script: Tab falls through to traversal (field refocused, wrap-around)"
      (← (← uiTest).ctx.window.textInputActive)

/-! ## Min-width knob + overflow safety (MT framework) -/

private def minWidthOverflow : IO Unit := do
  -- A field in a Row narrower than the 280 dp default min: it clamps to fit
  -- rather than forcing the Row to overflow (which once collapsed it to zero
  -- height). The Row keeps a real, non-zero height.
  let v1 ← MutableState.create ({} : TextFieldValue)
  runComposeTest (width := 400)
    (Row (modifier := Modifier.width 120 |>.testTag "row") do
      Tests.restartable 1 do ValueTextField (← v1.get) v1.set (modifier := Modifier.testTag "tf"))
    do
      let tf ← boundsOf (.tag "tf")
      let row ← boundsOf (.tag "row")
      check s!"minWidth: field clamped into the 120 dp Row (w={tf.right - tf.left})"
        (tf.right - tf.left ≤ 120)
      check s!"minWidth: Row keeps a non-zero height (h={row.bottom - row.top})"
        (row.bottom - row.top ≥ 40)
  -- The `minWidth` knob shrinks the field's floor so it fits a small parent
  -- even when width is unbounded (a horizontally scrolling Row) — the default
  -- 280 would report 280 there.
  let v2 ← MutableState.create ({} : TextFieldValue)
  runComposeTest (width := 400)
    (do
      let sc ← rememberScrollState
      Row (modifier := Modifier.horizontalScroll sc) do
        Tests.restartable 1 do
          ValueTextField (← v2.get) v2.set (minWidth := 60) (modifier := Modifier.testTag "tf2"))
    do
      let tf ← boundsOf (.tag "tf2")
      check s!"minWidth knob: unbounded field honors the 60 dp floor (w={tf.right - tf.left})"
        (tf.right - tf.left ≤ 80)

/-! ## macOS line-motion keys (⌘, MT framework) -/

private def macKeys : IO Unit := do
  let value ← MutableState.create ({} : TextFieldValue)
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  runComposeTest (fieldContent value calls) do
    typeText (.tag "field") "hello world"            -- caret at 11
    pressKey .left (mods := .lGui)                    -- ⌘-Left = Home
    checkEq "mac: ⌘-Left goes to the line start" (← value.get)
      (⟨"hello world", .caret 0, none⟩)
    pressKey .right (mods := .lGui)                   -- ⌘-Right = End
    checkEq "mac: ⌘-Right goes to the line end" (← value.get)
      (⟨"hello world", .caret 11, none⟩)
    pressKey .left (mods := .lGui ||| .lShift)        -- ⌘-Shift-Left selects to start
    checkEq "mac: ⌘-Shift-Left selects to the line start" (← value.get)
      (⟨"hello world", ⟨11, 0⟩, none⟩)
    pressKey .«end»                                   -- collapse to the end
    pressKey .backspace (mods := .lGui)               -- ⌘-Backspace deletes to line start
    checkEq "mac: ⌘-Backspace clears to the line start" (← value.get)
      (⟨"", .caret 0, none⟩)

/-! ## Multi-byte safety (MT framework) -/

private def multiByteEditing : IO Unit := do
  let value ← MutableState.create ({} : TextFieldValue)
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  runComposeTest (fieldContent value calls) do
    typeText (.tag "field") "héllo"
    checkEq "utf8: typed multi-byte text" (← value.get) (⟨"héllo", .caret 6, none⟩)
    pressKey .backspace
    checkEq "utf8: backspace removes one codepoint" (← value.get)
      (⟨"héll", .caret 5, none⟩)
    pressKey .left
    pressKey .left
    pressKey .left
    checkEq "utf8: three Lefts step over é as one unit" (← value.get)
      (⟨"héll", .caret 1, none⟩)
    pressKey .delete
    checkEq "utf8: Delete removes the 2-byte é whole" (← value.get)
      (⟨"hll", .caret 1, none⟩)
    typeText (.tag "field") "日本語"
    checkEq "utf8: CJK commits insert at the caret" (← value.get)
      (⟨"h日本語ll", .caret 10, none⟩)
    pressKey .backspace
    checkEq "utf8: backspace eats one 3-byte codepoint" (← value.get)
      (⟨"h日本ll", .caret 7, none⟩)

/-! ## Mouse: caret, drag selection, double/triple click -/

private def mouseSelection : IO Unit := do
  let text := "hello world"
  let (r, value, _) ← fieldRig (initial := { text, selection := .caret 0 })
  -- Click between glyphs 3 and 4 (just right of boundary 3): caret at 3.
  let x3 ← caretScreenX r text 3
  r.click (x3 + 1) 20
  r.pump
  checkEq "mouse: click sets the caret at the glyph boundary" (← value.get)
    (⟨text, .caret 3, none⟩)
  -- Click past the end of the text: caret at the end.
  r.click 200 20
  r.pump
  checkEq "mouse: click past the text end parks the caret at the end"
    (← value.get) (⟨text, .caret 11, none⟩)
  -- Drag from byte 2 to byte 8 selects [2, 8) with the anchor at the press.
  let x2 ← caretScreenX r text 2
  let x8 ← caretScreenX r text 8
  r.press (x2 + 1) 20
  r.move (x8 + 1) 20
  r.release (x8 + 1) 20
  r.pump
  checkEq "mouse: drag selects from the press anchor" (← value.get)
    (⟨text, ⟨2, 8⟩, none⟩)
  -- Dragging backwards keeps the anchor and inverts the active end.
  r.press (x8 + 1) 20
  r.move (x2 + 1) 20
  r.release (x2 + 1) 20
  r.pump
  checkEq "mouse: backwards drag inverts anchor/active" (← value.get)
    (⟨text, ⟨8, 2⟩, none⟩)
  -- Selection highlight pixels: primary@40% over white between the carets,
  -- plain white outside the selection (row above the glyphs).
  let selColor := (L.primary.withAlpha 0.40).compositeOver .white
  let sy : Int32 := 12   -- selection band top (textTop 10 .. 30), above glyph tops
  let inX := ((x2 + x8) / 2).toInt32
  check s!"mouse: selection highlight present ({Tests.Harness.showColor (← r.pixel inX sy)})"
    (near (← r.pixel inX sy) selColor 12)
  let x10 ← caretScreenX r text 10
  check "mouse: no highlight outside the selection"
    (near (← r.pixel (x10.toInt32 + 2) sy) .white 12)
  -- Double-click on 'world' selects the word.
  let x8b ← caretScreenX r text 8
  r.click (x8b + 1) 20 (clicks := 2)
  r.pump
  checkEq "mouse: double-click selects the word" (← value.get)
    (⟨text, ⟨6, 11⟩, none⟩)
  -- Triple-click selects everything.
  r.click (x8b + 1) 20 (clicks := 3)
  r.pump
  checkEq "mouse: triple-click selects all" (← value.get)
    (⟨text, ⟨0, 11⟩, none⟩)
  -- I-beam hover cursor is declared on the chain (root.child 0 is the
  -- backdrop-blur wrapper; the app content sits under it).
  let d ← (← (← r.ctx.root.child 0).child 0).data
  check "mouse: I-beam hover icon on the field"
    (d.modifier.elems.any (· matches .pointer (.hoverIcon .text)))

/-! ## Clipboard -/

private def clipboardOps : IO Unit := do
  let text := "hello world"
  let (r, value, _) ← fieldRig (initial := { text, selection := .caret 0 })
  r.click 100 20
  r.pump
  -- Copy the selected word.
  r.click (← caretScreenX r text 8) 20 (clicks := 2)   -- select "world"
  r.pump
  r.key .c (mods := .lCtrl)
  checkEq "clipboard: copy puts the selection on the clipboard"
    (← Sdl.getClipboardText) "world"
  checkEq "clipboard: copy leaves the value alone" (← value.get)
    (⟨text, ⟨6, 11⟩, none⟩)
  -- Paste (gui mod) replaces the selection, newlines stripped.
  Sdl.setClipboardText "W\nO\rRLD"
  r.key .v (mods := .lGui)
  r.pump
  checkEq "clipboard: paste replaces the selection, single-line sanitized"
    (← value.get) (⟨"hello WORLD", .caret 11, none⟩)
  -- Cut: clipboard gets the selection, text loses it.
  r.key .a (mods := .lGui)
  r.key .x (mods := .lCtrl)
  r.pump
  checkEq "clipboard: cut removes the selection" (← value.get) (⟨"", .caret 0, none⟩)
  checkEq "clipboard: cut copied first" (← Sdl.getClipboardText) "hello WORLD"
  -- Copy with a collapsed caret leaves the clipboard alone.
  r.key .c (mods := .lCtrl)
  checkEq "clipboard: caret-only copy is a no-op" (← Sdl.getClipboardText) "hello WORLD"

/-! ## IME composition -/

private def imeComposition : IO Unit := do
  let (r, value, _) ← fieldRig
  r.click 100 20
  r.pump
  -- Composition grows through successive textEditing events.
  r.editing "a" 1 0
  r.pump
  checkEq "ime: first composition set" (← value.get)
    (⟨"a", .caret 1, some ⟨0, 1⟩⟩)
  r.editing "abc" 3 0
  r.pump
  checkEq "ime: successive setComposition replaces the region" (← value.get)
    (⟨"abc", .caret 3, some ⟨0, 3⟩⟩)
  -- Underline pixels: 1 px under the composed span (below the glyph boxes),
  -- absent right of it.
  let l ← probeLayout r "abc"
  let wAbc := (← l.measure none).width
  let uy : Int32 := 29   -- textTop 10 + lineHeight 20 - 1
  check s!"ime: composition underline drawn ({Tests.Harness.showColor (← r.pixel 14 uy)})"
    (near (← r.pixel 14 uy) L.onSurface 60)
  check "ime: no underline past the composition"
    (near (← r.pixel (14 + wAbc + 4) uy) .white)
  -- Commit replaces the composition and clears it.
  r.text "ABC"
  r.pump
  checkEq "ime: commit replaces the composition" (← value.get)
    (⟨"ABC", .caret 3, none⟩)
  check "ime: underline gone after the commit" (near (← r.pixel 14 uy) .white)
  -- Cursor position inside the composition (codepoint-indexed).
  r.editing "xyz" 1 0
  r.pump
  checkEq "ime: composition cursor honored (codepoint 1 → byte 1 within)"
    (← value.get) (⟨"ABCxyz", .caret 4, some ⟨3, 6⟩⟩)
  -- Empty composition cancels.
  r.editing "" 0 0
  r.pump
  checkEq "ime: empty setComposition cancels" (← value.get) (⟨"ABC", .caret 3, none⟩)

/-- The Android IME stream contract: SDL's `InputConnection` greedily
commits provisional text and repairs recompositions as backspace *keys*
plus fresh commits (Vietnamese Telex "Mo" → "Mộ" arrives as ⌫ + "ộ") —
composition events never reach the app on Android. The field must apply
the interleaved key/text stream in order, and a word typed after
backspacing to empty must never resurrect old text. -/
private def imeGreedyCommitRepair : IO Unit := do
  let (r, value, _) ← fieldRig
  r.click 100 20
  r.pump
  -- "Một" via Telex repair: M, o, ⌫+ộ, t.
  r.text "M"
  r.text "o"
  r.key .backspace
  r.text "ộ"
  r.pump
  checkEq "ime repair: backspace+commit recomposes in place" (← value.get)
    (⟨"Mộ", .caret 4, none⟩)
  r.text "t"
  r.pump
  checkEq "ime repair: the word completes" (← value.get)
    (⟨"Một", .caret 5, none⟩)
  -- Backspace to empty (three codepoints), then a fresh word: nothing of
  -- the old one may leak back.
  r.key .backspace
  r.key .backspace
  r.key .backspace
  r.pump
  checkEq "ime repair: backspaced to empty" (← value.get) (⟨"", .caret 0, none⟩)
  r.text "H"
  r.text "a"
  r.text "i"
  r.pump
  checkEq "ime repair: a fresh word starts clean" (← value.get)
    (⟨"Hai", .caret 3, none⟩)

/-- IME session lifecycle: `startTextInput` on focusing a field,
`stopTextInput` on leaving; the caret area follows the caret. -/
private def imeSession : IO Unit := do
  let (r, _, _) ← fieldRig
  check "ime session: inactive before focus" (!(← r.ctx.window.textInputActive))
  r.click 100 20
  check "ime session: click-to-focus starts text input"
    (← r.ctx.window.textInputActive)
  r.pump
  -- The published input area covers the field box in window coordinates.
  let (rect, cur0) ← r.ctx.window.getTextInputArea
  checkEq "ime session: input area matches the field box"
    (rect.x, rect.y, rect.w, rect.h) ((0 : Int32), (0 : Int32), (240 : Int32), (40 : Int32))
  r.text "hello"
  r.pump
  let (_, cur1) ← r.ctx.window.getTextInputArea
  check s!"ime session: caret offset advanced with typing ({cur0} → {cur1})"
    (cur1 > cur0)
  r.key .escape
  check "ime session: Esc clears focus and stops text input"
    (!(← r.ctx.window.textInputActive))

/-! ## Caret blink -/

/-- Leftmost pixel near `color` in `[x0, x1) × {y}`. -/
private def findColorX (r : TRig) (y : Int32) (x0 x1 : Int32) (color : Compose.Color)
    (tol : Nat := 40) : IO (Option Int32) := do
  let surf ← (← r.ctx.sdlRenderer).readPixels
  for x in [x0.toNatClampNeg : x1.toNatClampNeg] do
    if near (← surf.readPixel (Int32.ofNat x) y) color tol then
      return some (Int32.ofNat x)
  return none

private def caretBlink : IO Unit := do
  let (r, _, _) ← fieldRig
  -- Unfocused: no caret anywhere in the text row interior.
  check "blink: no caret while unfocused"
    ((← findColorX r 20 4 236 L.primary) == none)
  r.click 100 20
  r.pump   -- blink phase ≈ 24 ms: caret on
  let on0 ← findColorX r 20 4 236 L.primary
  check s!"blink: caret visible right after focus ({on0})"
    (on0.any fun x => x ≥ 12 && x ≤ 15)
  r.tick 600   -- phase ≈ 0.6: caret off
  check "blink: caret hidden mid-cycle" ((← findColorX r 20 4 236 L.primary) == none)
  r.tick 450   -- phase wraps: caret on again
  check "blink: caret returns next cycle"
    ((← findColorX r 20 4 236 L.primary).isSome)
  r.key .escape
  r.pump
  check "blink: unfocused again → no caret"
    ((← findColorX r 20 4 236 L.primary) == none)

/-! ## Horizontal auto-scroll -/

private def autoScroll : IO Unit := do
  let text := String.join (List.replicate 6 "abcdefghij")   -- 60 chars, ≫ 100 dp
  let (r, value, _) ← fieldRig (initial := { text, selection := .caret 0 })
    (fieldWidth := some 100)
  let sz ← (← r.ctx.root.child 0).size
  checkEq "scroll: field clamped to its 100 dp width" sz.width 100
  r.click 50 20
  r.pump
  r.key .«end»
  r.pump
  checkEq "scroll: End moved the caret to the last byte"
    (← value.get).selection.active 60
  -- The caret is visible near the right edge of the inner box (12..88),
  -- inside the field — i.e. the text scrolled.
  let caretAtEnd ← findColorX r 20 4 96 L.primary
  check s!"scroll: caret visible near the right edge ({caretAtEnd})"
    (caretAtEnd.any fun x => x ≥ 60 && x ≤ 89)
  -- The text start scrolled out: the first glyphs are no longer at pad 12
  -- (probe: the glyph column pattern at x 13 differs from an unscrolled
  -- render — cheap proxy: 'a' has a dark pixel at x≈13 when unscrolled).
  r.key .home
  r.pump
  let caretAtHome ← findColorX r 20 4 96 L.primary
  check s!"scroll: Home scrolls back, caret at the left edge ({caretAtHome})"
    (caretAtHome.any fun x => x ≥ 12 && x ≤ 15)

/-! ## Look: outline states, placeholder, label strip -/

private def outlineStates : IO Unit := do
  -- Unfocused: 1 dp outline.
  let (r, _, _) ← fieldRig
  check s!"outline: unfocused stroke is `outline` ({Tests.Harness.showColor (← r.pixel 120 0)})"
    (near (← r.pixel 120 0) L.outline 40)
  check "outline: interior is the clear color" (near (← r.pixel 120 20) .white)
  -- Focused: 2 dp primary.
  r.click 100 20
  r.pump
  check s!"outline: focused stroke is primary ({Tests.Harness.showColor (← r.pixel 120 1)})"
    (near (← r.pixel 120 1) L.primary 40)
  -- Error: error-colored outline (focused or not).
  let (re, _, _) ← fieldRig (isError := true)
  check s!"outline: isError stroke is error ({Tests.Harness.showColor (← re.pixel 120 0)})"
    (near (← re.pixel 120 0) L.error 40)
  -- Disabled: no focus on click, no edits on keys.
  let (rd, dvalue, dcalls) ← fieldRig (enabled := false)
  rd.click 100 20
  rd.pump
  check "outline: disabled field takes no focus" (!(← rd.ctx.window.textInputActive))
  rd.text "nope"
  rd.key .backspace
  rd.pump
  checkEq "outline: disabled field ignores input" (← dvalue.get) ({} : TextFieldValue)
  checkEq "outline: disabled field fired no callbacks" (← dcalls.get).size 0

private def placeholderAndLabel : IO Unit := do
  -- Placeholder glyphs only while empty.
  let (r, _, _) ← fieldRig (placeholder := "MMMMM")
  let countDark (r : TRig) (x0 x1 : Nat) : IO Nat := do
    let surf ← (← r.ctx.sdlRenderer).readPixels
    let mut n := 0
    for y in [12:28] do
      for x in [x0:x1] do
        let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
        if c.r < 140 && c.g < 140 && c.b < 140 then n := n + 1
    return n
  let empty ← countDark r 14 80
  check s!"placeholder: glyphs shown while empty ({empty})" (empty > 0)
  r.click 100 20
  r.pump
  r.text "i"   -- a narrow glyph: the 30..80 band would still be covered by "MMMMM"
  r.pump
  let afterTyping ← countDark r 30 80
  checkEq s!"placeholder: hidden once the field has text" afterTyping 0
  -- Label: reserves the 14 dp strip; floats up when focused.
  let (rl, _, _) ← fieldRig (label := some "Name")
  let sz ← (← rl.ctx.root.child 0).size
  checkEq "label: node reserves the label strip (40 + 14)" sz.height 54
  check "label: outline moved below the strip" (near (← rl.pixel 120 14) L.outline 40)
  check "label: strip starts clear (label resting inside)" (near (← rl.pixel 16 2) .white)
  -- Resting label glyphs sit at the text position.
  let restBand ← countDark rl 14 60
  check s!"label: resting label glyphs in the text band ({restBand})" (restBand > 0)
  rl.click 100 34
  for _ in [0:30] do rl.tick 8   -- let the float animation settle
  -- Floating label: primary-ish glyphs in the strip.
  let surf ← (← rl.ctx.sdlRenderer).readPixels
  let mut floatPix := 0
  for y in [0:13] do
    for x in [12:70] do
      let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if near c L.primary 70 && c.r < 220 then floatPix := floatPix + 1
  check s!"label: floats into the strip when focused ({floatPix})" (floatPix > 0)

/-! ## TextField (String convenience, MT framework) -/

private def stringOverload : IO Unit := do
  let value ← MutableState.create ""
  let calls ← IO.mkRef (#[] : Array String)
  runComposeTest
    (Tests.restartable 1 do
      TextField (← value.get) (fun s => do calls.modify (·.push s); value.set s)
        (modifier := Modifier.testTag "field"))
    do
      typeText (.tag "field") "hi"
      checkEq "textfieldS: string callback saw each commit" (← calls.get) #["h", "hi"]
      assertTextEquals (.tag "field") "hi"
      checkEq "textfieldS: state is the string" (← value.get) "hi"
      -- Selection is managed internally: motions/backspace need no callbacks.
      pressKey .left
      pressKey .backspace
      assertTextEquals (.tag "field") "i"
      checkEq "textfieldS: only text changes are reported" (← calls.get)
        #["h", "hi", "i"]
      -- External rewrite: the app replaces the text; the caret clamps.
      value.set "reset"
      awaitIdle
      pressKey .«end»
      typeText (.tag "field") "!"
      assertTextEquals (.tag "field") "reset!"
      checkEq "textfieldS: external value change accepted" (← value.get) "reset!"

/-- The TextField group. -/
def run : IO Unit := do
  typingEndToEnd
  editingScripts
  minWidthOverflow
  macKeys
  multiByteEditing
  mouseSelection
  touchFieldGesture
  touchLongPress
  touchSelectionHandles
  touchSelectionToolbar
  touchChromeEdges
  imeSyncHook
  clipboardOps
  imeComposition
  imeGreedyCommitRepair
  imeSession
  caretBlink
  autoScroll
  outlineStates
  placeholderAndLabel
  stringOverload

end Tests.TextField
