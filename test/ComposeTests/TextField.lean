import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# TextField test group (`test/ComposeTests/TextField.lean`)

M11's end-to-end editing suites, headless. The value-flow suites (typing,
editing scripts, UTF-8, `TextFieldS`) are written in the MT framework
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
      (MaterialTheme (content := content))) cfg
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
  (← r.ctx.renderer.readPixels).readPixel x y

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

/-- Boot a controlled `TextField` bound to fresh state; returns the rig, the
state, and the change log. -/
private def fieldRig (initial : TextFieldValue := {}) (w : Dp := 240)
    (placeholder : String := "") (label : Option String := none)
    (isError : Bool := false) (enabled : Bool := true) (fieldWidth : Option Dp := none) :
    IO (TRig × MutableState TextFieldValue × IO.Ref (Array TextFieldValue)) := do
  let value ← mutableStateOf initial
  let calls ← IO.mkRef (#[] : Array TextFieldValue)
  let m := match fieldWidth with
    | some fw => Modifier.width fw
    | none => {}
  let r ← tboot (w := w) <| Tests.restartable 1 do
    let v ← value.get
    TextField v (fun v' => do calls.modify (·.push v'); value.set v')
      (modifier := m) (enabled := enabled) (isError := isError)
      (placeholder := placeholder) (label := label)
  return (r, value, calls)

/-! ## End-to-end typing (controlled loop, MT framework) -/

/-- One tagged controlled `TextField` bound to `value`, logging every
`onValueChange` into `calls` — the content of the MT-framework suites. -/
private def fieldContent (value : MutableState TextFieldValue)
    (calls : IO.Ref (Array TextFieldValue)) : Composable Unit :=
  Tests.restartable 1 do
    let v ← value.get
    TextField v (fun v' => do calls.modify (·.push v'); value.set v')
      (modifier := Modifier.testTag "field")

private def typingEndToEnd : IO Unit := do
  let value ← mutableStateOf ({} : TextFieldValue)
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
  let value ← mutableStateOf ({} : TextFieldValue)
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
    pressKey .right (mods := .lGui)                  -- gui word-right (macOS)
    checkEq "script: gui-Right word-jumps" (← value.get)
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

/-! ## Multi-byte safety (MT framework) -/

private def multiByteEditing : IO Unit := do
  let value ← mutableStateOf ({} : TextFieldValue)
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
  -- I-beam hover cursor is declared on the chain.
  let d ← (← r.ctx.root.child 0).data
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
  let surf ← r.ctx.renderer.readPixels
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
    let surf ← r.ctx.renderer.readPixels
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
  let surf ← rl.ctx.renderer.readPixels
  let mut floatPix := 0
  for y in [0:13] do
    for x in [12:70] do
      let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if near c L.primary 70 && c.r < 220 then floatPix := floatPix + 1
  check s!"label: floats into the strip when focused ({floatPix})" (floatPix > 0)

/-! ## TextFieldS (String convenience, MT framework) -/

private def stringOverload : IO Unit := do
  let value ← mutableStateOf ""
  let calls ← IO.mkRef (#[] : Array String)
  runComposeTest
    (content := Tests.restartable 1 do
      TextFieldS (← value.get) (fun s => do calls.modify (·.push s); value.set s)
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
  multiByteEditing
  mouseSelection
  clipboardOps
  imeComposition
  imeSession
  caretBlink
  autoScroll
  outlineStates
  placeholderAndLabel
  stringOverload

end Tests.TextField
