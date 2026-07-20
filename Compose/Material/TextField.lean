module

public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Ui.Text.EditModel
public meta import Compose.Ui.Text.EditModel
public import Compose.Animation.Transition
public meta import Compose.Animation.Transition
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout
public import Compose.Material.TextFieldChrome
public meta import Compose.Material.TextFieldChrome

public section

namespace Compose

open Draw

/-!
# TextField (`Compose/Material/TextField.lean`)

The M11 outlined single-line text field, mirroring
`androidx.compose.material3.OutlinedTextField` on the M9 diet:

- **Look**: 1 dp `outline` border on `shapes.extraSmall` (2 dp `primary` when
  focused, `error` when `isError`), min height 40 dp, 12 dp horizontal
  content padding, placeholder in `onSurfaceVariant`, disabled content at the
  Material 38 %/12 % alphas.
- **Label**: when a `label` is given the node reserves a 14 dp strip above
  the outline; the label continuously animates its font size (text size ↔
  11 sp) and position between the placeholder position (empty + unfocused)
  and that strip, driven by `animateFloatAsState` (one layout rebuilt at the
  interpolated size, like M3 animating the label's textStyle). *Documented
  deviation*: M3 floats the label onto the outline, cutting a gap into the
  stroke — the reserved-strip variant avoids outline surgery.
- **Editing**: all edits go through the pure `EditModel`
  (`TextFieldValue.apply`); the field is a **controlled component** — it
  never owns the value, every edit is reported through `onValueChange` and
  the caller echoes it back. An internal "latest value" ref is updated
  optimistically after each self-applied edit so events arriving between
  recompositions (fast typing, key repeat) compose correctly; recomposition
  re-synchronizes it with the authoritative `value` prop.
- **Caret**: 1.5 dp bar at the selection's `active` end, blinking at ~1 Hz
  through `rememberInfiniteTransition` (composed only while focused, so an
  idle field schedules no frames).
- **Selection**: one `primary`@40 % rect from the start caret x to the end
  caret x (single line), under the glyphs, drawn while focused.
- **IME**: committed text inserts via `Modifier.onTextInput`; composition
  updates arrive via `Modifier.onTextEditing` → `EditCommand.setComposition`
  (underlined 1 dp); the caret area is published with
  `Window.setTextInputArea` whenever it moves (the session start/stop lives
  in `Compose.bootstrap`).
- **Mouse**: click places the caret (nearest boundary), drag selects from
  the press anchor, double-click selects the word, triple-click selects all;
  I-beam hover cursor.
- **Touch selection chrome**: a finger long-press selects the word and
  raises floating drag handles; the settling finger adds a Cut/Copy/Paste
  toolbar above the selection (`TextFieldChrome` — focus-neutral popups
  anchored off draw-pass geometry). Touch-only: mouse/keyboard selection
  never shows chrome. Chrome hides on edit, selection collapse, focus
  loss, and Esc/back — the selection itself persists. An enclosing scroll
  moves the handles with the text (the toolbar sits the motion out and
  returns); chrome scrolled out of the viewport is suppressed.
- **Keyboard**: arrows/Home/End with Shift extension, ctrl/alt word variants,
  gui (⌘) line variants (⌘-Left/Right = Home/End, ⌘-Backspace/Delete =
  delete-to-line-start/end — macOS habits, accepted on every platform),
  Backspace/Delete (+word), ctrl-or-gui A/C/V/X via the SDL clipboard. Tab/Esc
  are left unconsumed for the focus fallbacks. Key repeat arrives as extra
  key-downs and is handled per event.
- **Auto-scroll**: text wider than the box scrolls horizontally so the caret
  stays visible; hit testing compensates.

`singleLine := true` is the only supported mode (DESIGN.md scopes the
TextField to single-line); the flag exists for API fidelity and controls
newline stripping on insert/paste.

`TextField` is the `String`-convenience overload the 7GUIs demos consume: it
remembers the selection/composition internally and reports plain strings.
-/

/-! ## Key mapping (pure) -/

/-- What a key press asks of the field: an `EditModel` command or a clipboard
action. -/
inductive TextFieldKeyAction where
  | edit (cmd : EditCommand)
  | copy
  | cut
  | paste
  deriving Repr, BEq

/-- Whether a shortcut modifier is held: Ctrl **or** Gui (⌘ — macOS delivers
command shortcuts with `gui`). -/
def isShortcutMod (m : Sdl.Keymod) : Bool :=
  (m &&& (Sdl.Keymod.ctrl ||| Sdl.Keymod.gui)) != Sdl.Keymod.none

/-- Whether a word-motion modifier is held: Ctrl or Alt (macOS word motions
are option-arrows, Ctrl covers Windows/Linux; ⌘/Gui is reserved for
line-motions, see `isLineMod`). -/
def isWordMod (m : Sdl.Keymod) : Bool :=
  (m &&& (Sdl.Keymod.ctrl ||| Sdl.Keymod.alt)) != Sdl.Keymod.none

/-- Whether a line-motion modifier is held: Gui (⌘). macOS binds ⌘-Left/Right
to line start/end and ⌘-Backspace to delete-to-line-start; SDL delivers ⌘ as
`gui`. Accepted unconditionally (no platform gate) alongside Home/End — the
Super key is otherwise unused for text editing on other desktops. -/
def isLineMod (m : Sdl.Keymod) : Bool :=
  (m &&& Sdl.Keymod.gui) != Sdl.Keymod.none

/-- Map a key event to the field action it requests (`none` = not ours; Tab
and Esc always fall through to the focus fallbacks). Key repeat is a fresh
key-down and maps like the first press. -/
def textFieldKeyAction (ke : KeyEvent) : Option TextFieldKeyAction :=
  if !ke.down then none
  else
    let shift := ke.hasShift
    let word := isWordMod ke.mods
    let line := isLineMod ke.mods
    let short := isShortcutMod ke.mods
    match ke.key with
    | .left =>
      some (.edit (if line then .home shift else if word then .wordLeft shift else .left shift))
    | .right =>
      some (.edit (if line then .«end» shift else if word then .wordRight shift else .right shift))
    | .home => some (.edit (.home shift))
    | .«end» => some (.edit (.«end» shift))
    | .backspace =>
      some (.edit (if line then .deleteToLineStart else if word then .deleteWordBack else .backspace))
    | .delete =>
      some (.edit (if line then .deleteToLineEnd else if word then .deleteWordForward else .deleteForward))
    | .a => if short then some (.edit .selectAll) else none
    | .c => if short then some .copy else none
    | .v => if short then some .paste else none
    | .x => if short then some .cut else none
    | _ => none

#guard textFieldKeyAction { key := .left } == some (.edit (.left false))
#guard textFieldKeyAction { key := .left, mods := .lShift } == some (.edit (.left true))
#guard textFieldKeyAction { key := .left, mods := .lCtrl } == some (.edit (.wordLeft false))
#guard textFieldKeyAction { key := .left, mods := .lAlt } == some (.edit (.wordLeft false))
-- ⌘ (gui) makes arrows line-motions (macOS Home/End), keeping Shift extension.
#guard textFieldKeyAction { key := .left, mods := .lGui } == some (.edit (.home false))
#guard textFieldKeyAction { key := .right, mods := .lGui } == some (.edit (.«end» false))
#guard textFieldKeyAction { key := .right, mods := .lGui ||| .lShift }
        == some (.edit (.«end» true))
#guard textFieldKeyAction { key := .home, mods := .lShift } == some (.edit (.home true))
#guard textFieldKeyAction { key := .«end» } == some (.edit (.«end» false))
#guard textFieldKeyAction { key := .backspace } == some (.edit .backspace)
#guard textFieldKeyAction { key := .backspace, mods := .lCtrl } == some (.edit .deleteWordBack)
-- ⌘-Backspace / ⌘-Delete delete to the line start / end.
#guard textFieldKeyAction { key := .backspace, mods := .lGui } == some (.edit .deleteToLineStart)
#guard textFieldKeyAction { key := .delete } == some (.edit .deleteForward)
#guard textFieldKeyAction { key := .delete, mods := .lGui } == some (.edit .deleteToLineEnd)
#guard textFieldKeyAction { key := .delete, mods := .lCtrl } == some (.edit .deleteWordForward)
#guard textFieldKeyAction { key := .a, mods := .lCtrl } == some (.edit .selectAll)
#guard textFieldKeyAction { key := .a, mods := .lGui } == some (.edit .selectAll)
#guard textFieldKeyAction { key := .a } == none                    -- plain letter: IME's
#guard textFieldKeyAction { key := .c, mods := .lCtrl } == some .copy
#guard textFieldKeyAction { key := .v, mods := .lGui } == some .paste
#guard textFieldKeyAction { key := .x, mods := .lCtrl } == some .cut
#guard textFieldKeyAction { key := .c, mods := .lAlt } == none     -- alt is not a shortcut mod
#guard textFieldKeyAction { key := .tab } == none
#guard textFieldKeyAction { key := .escape } == none
#guard textFieldKeyAction { key := .left, down := false } == none
#guard textFieldKeyAction { key := .backspace, isRepeat := true } == some (.edit .backspace)

/-- Drop CR/LF (single-line fields paste/insert flattened text). -/
def stripNewlines (s : String) : String :=
  if s.any (fun c => c == '\n' || c == '\r') then
    s.foldl (init := "") fun acc c =>
      if c == '\n' || c == '\r' then acc else acc.push c
  else s

#guard stripNewlines "ab" == "ab"
#guard stripNewlines "a\nb\r\nc" == "abc"
#guard stripNewlines "\n" == ""

/-! ## Internal plumbing -/

/-- Height (dp) of the strip reserved above the outline for a floating label. -/
private def labelStripDp : Dp := 14

/-- Horizontal content padding (dp). -/
private def contentPadDp : Dp := 12

/-- The live callbacks the long-lived pointer coroutine reads per event (the
`rememberUpdatedRef` pattern — the coroutine relaunches on `enabled` change
only). -/
private structure FieldGestureParams where
  enabled : Bool
  /-- Element-local position → caret byte offset (nearest boundary, scroll
  compensated). -/
  hitCaret : Offset → IO Nat
  /-- Apply an edit and report it (see `TextField`'s controlled contract). -/
  edit : EditCommand → IO Unit
  /-- A finger tap landed on the field while it was *already* focused:
  re-show the soft keyboard the user may have dismissed. Focus-gain taps
  start text input through the focus hook instead — `SDL_StartTextInput`
  is a no-op while text input is active, so this bounces it. -/
  reshowKeyboard : IO Unit
  /-- Select the word at an element-local position and return the resulting
  selection — the finger long-press entry, returning the word range the
  selection drag anchors to. -/
  selectWord : Offset → IO TextRange
  /-- A finger long-press selected a word: show the selection chrome. -/
  chromeShow : IO Unit
  /-- The selecting finger lifted (or the gesture was cancelled): the
  selection settled — the chrome's toolbar may appear. -/
  chromeSettle : IO Unit

private instance : Nonempty FieldGestureParams :=
  ⟨{ enabled := false, hitCaret := fun _ => pure 0, edit := fun _ => pure ()
     reshowKeyboard := pure (), selectWord := fun _ => pure {}
     chromeShow := pure (), chromeSettle := pure () }⟩

/-- Finger long-press timeout, ms (Android's `LONG_PRESS_TIMEOUT`; matches
`detectTapGestures`' default). -/
private def fieldLongPressMillis : UInt32 := 500

/-- How a finger contact on the field resolved: the long-press timer won, or
the tap wait ended first (release, cancel, or an enclosing scroll's steal). -/
private inductive FingerFieldOutcome where
  | longPressed
  | ended

/-- The caret/selection gesture.

Mouse (pointer `0`): press places the caret (or selects the word on
double-click / everything on triple-click, via SDL's consecutive-click
counter), dragging extends the selection from the press anchor. Presses,
drag moves, and releases are consumed.

Finger: a *tap* places the caret at the release (focus commits in the
router at the same up — Android focuses on the tap, not the touch-down),
while a drag belongs to an enclosing scrollable: moves stay unconsumed so
a drag-scroll's slop tracking sees them, and its steal cancels the tap
(the capture cut delivers `exit`). Press and release are consumed (an
outer clickable must not also fire). A *long-press* (the finger holds
`fieldLongPressMillis` before releasing, drifting past slop, or being
stolen) selects the word under the press and switches to a selection drag:
from there moves are consumed and extend the selection word-to-caret
(Android's word-anchored extension), which also parks the enclosing scroll
— its tracker stands off from a consumed gesture. The long-press also
raises the selection chrome (floating handles, then the toolbar when the
finger settles — see `TextFieldChrome`); mouse selection never does. -/
private partial def fieldGesture (params : IO.Ref FieldGestureParams)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    let p ← params.get
    if p.enabled then
      if ev.pointerId == 0 then
        ev.consume
        let off ← p.hitCaret ev.position
        if ev.clicks ≥ 3 then
          p.edit .selectAll
          awaitRelease
        else if ev.clicks == 2 then
          p.edit (.selectWord off)
          awaitRelease
        else
          p.edit (.setSelection (.caret off))
          dragLoop off
      else
        ev.consume
        let pid := ev.pointerId
        let pressPos := ev.position
        -- Race the long-press timer against the tap wait: a raced-out
        -- awaiter's event is buffered, not swallowed (`offer`), so either
        -- winner leaves the stream intact.
        match ← UiTask.race
            (do UiTask.delay fieldLongPressMillis; pure FingerFieldOutcome.longPressed)
            (do fingerTap pid; pure .ended) with
        | .ended => pure ()
        | .longPressed =>
          let p ← params.get
          let word ← p.selectWord pressPos
          p.chromeShow
          selDrag pid word
  fieldGesture params scope
where
  /-- Await the finger tap's release: place the caret there. Moves pass
  through unconsumed (an enclosing drag-scroll may take the gesture; its
  steal ends this wait with the capture-cut `exit`). -/
  fingerTap (pid : UInt64) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then fingerTap pid else
    match ev.eventType with
    | .release =>
      ev.consume
      let p ← params.get
      p.edit (.setSelection (.caret (← p.hitCaret ev.position)))
      p.reshowKeyboard
    | .exit => pure ()
    | _ => fingerTap pid
  /-- Post-long-press selection drag: moves are consumed (the enclosing
  scroll's tracker stands off from a consumed gesture — the field owns the
  pointer now) and extend the selection from the long-pressed word,
  word-anchored: dragging past the word's start anchors at its end and vice
  versa; inside the word the whole word stays selected. Release keeps the
  selection; `exit` (window leave / system cancel) abandons the drag. -/
  selDrag (pid : UInt64) (word : TextRange) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then selDrag pid word else
    match ev.eventType with
    | .move =>
      ev.consume
      let p ← params.get
      let off ← p.hitCaret ev.position
      let lo := word.start
      let hi := word.«end»
      p.edit (.setSelection <|
        if off < lo then ⟨hi, off⟩
        else if off > hi then ⟨lo, off⟩
        else ⟨lo, hi⟩)
      selDrag pid word
    | .release =>
      ev.consume
      (← params.get).chromeSettle
    | .exit => (← params.get).chromeSettle
    | _ => selDrag pid word
  /-- Follow the press: anchor fixed at the press offset. -/
  dragLoop (anchor : Nat) : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .move =>
      ev.consume
      let p ← params.get
      p.edit (.setSelection ⟨anchor, ← p.hitCaret ev.position⟩)
      dragLoop anchor
    | .release => ev.consume
    | .exit => pure ()
    | _ => dragLoop anchor
  /-- Swallow the gesture tail after a word/all selection. -/
  awaitRelease : UiTask Unit := do
    let ev ← scope.awaitEvent
    match ev.eventType with
    | .release => ev.consume
    | .exit => pure ()
    | _ => awaitRelease

/-- Get (creating on first use) and reconcile the layout stored in `cell`
(the `Material.Text` pattern, kept out of the composable body). -/
private def obtainFieldLayout (cell : IO.Ref (Option TextLayout)) (tc : TextContext)
    (text : String) (style : TextStyle) (density : Density) : IO TextLayout := do
  match ← cell.get with
  | some l =>
    l.update text style density
    return l
  | none =>
    let l ← TextLayout.create tc.textEngine tc.fontStore text style density
    cell.set (some l)
    return l

/-- Shrink a rounded rect by `d` px on all sides (stroke centerline inset;
the `Compose.Ui.Layout` border idiom). -/
private def insetRR (rr : RoundRect) (d : Float32) : RoundRect :=
  let f (c : CornerRadius) : CornerRadius := ⟨max 0 (c.x - d), max 0 (c.y - d)⟩
  { rect := rr.rect.inflate (-d)
    topLeft := f rr.topLeft, topRight := f rr.topRight
    bottomRight := f rr.bottomRight, bottomLeft := f rr.bottomLeft }

/-- Everything `drawTextField` needs, sampled at composition time. -/
private structure FieldVisuals where
  layout : TextLayout
  placeholder? : Option TextLayout
  /-- The label laid out at the current interpolated font size (`none` when the
  field has no label). One layout, morphed each animation frame. -/
  label? : Option TextLayout
  value : TextFieldValue
  focused : Bool
  enabled : Bool
  caretOn : Bool
  labelProgress : Float32
  outlineColor : Color
  outlineWidth : Dp
  caretColor : Color
  selectionColor : Color
  textColor : Color
  shape : Shape
  hasLabel : Bool
  /-- Horizontal scroll offset (px), owned by the draw pass. -/
  scroll : IO.Ref Float32
  /-- The window, for `setTextInputArea` (`none` headless-composed). -/
  window? : Option WindowContext
  /-- Last published IME area `(x, y, w, h, caretX)` in window coordinates. -/
  lastImeArea : IO.Ref (Option (Int32 × Int32 × Int32 × Int32 × Int32))
  /-- Last `(text, selection)` pushed through the window's app→IME sync hook
  (dedup — the pair changes far less often than the draw pass runs). -/
  lastImeSync : IO.Ref (Option (String × TextRange))
  /-- Whether the touch selection chrome is up — when so, the draw pass
  publishes this frame's anchor geometry into `chromeAnchors`. -/
  chromeOn : Bool
  /-- The chrome anchor geometry cell (window px), read by the chrome popups
  composed next frame; `none` while chrome is down or the selection is
  collapsed. Writes dedup via the cell's structural-equality skip. -/
  chromeAnchors : MutableState (Option ChromeAnchors)
  /-- Whether the field's window position moved this frame (an enclosing
  container scrolling under shown chrome): the handles keep tracking, the
  toolbar sits the movement out. -/
  chromeMoving : MutableState Bool
  /-- Last frame's field window position, the movement detector's memory. -/
  chromePos : IO.Ref (Option (Float32 × Float32))

/-- Draw the whole field: outline, selection, text/placeholder, composition
underline, caret, label — and publish the IME caret area when it moved.
Also owns the horizontal auto-scroll: the offset is (re)computed here from
the caret x and the inner width, so the caret is always scrolled into view
by the time pixels land. -/
private def drawTextField (vis : FieldVisuals) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let px (dp : Dp) : Float32 := ctx.density.dpToPx dp
  let labelSpace := if vis.hasLabel then px labelStripDp else 0
  let boxH := sz.height - labelSpace
  -- Outline stroke just inside the box.
  let rr := vis.shape.toRoundRect ⟨sz.width, boxH⟩ ctx.density
  let ow := px vis.outlineWidth
  DrawScope.translate ⟨0, labelSpace⟩ <|
    DrawScope.drawRoundRect (.solid vis.outlineColor) (insetRR rr (ow / 2)) (.stroke ow)
  -- Text geometry.
  let pad := px contentPadDp
  let innerW := max 0 (sz.width - 2 * pad)
  let lineH := (← vis.layout.lineHeight).toFloat32
  let textTop := labelSpace + (boxH - lineH) / 2
  let textW := (← vis.layout.measure none).width.toFloat32
  let bytes := vis.value.text.utf8ByteSize
  -- Caret x in text-local coordinates (byte offset → glyph left edge).
  let xAt (off : Nat) : IO Float32 := do
    if vis.value.text.isEmpty then return 0
    if off ≥ bytes then return textW
    return (← vis.layout.byteOffsetToRect off).left
  let caretW := px 1.5
  let caretX ← xAt vis.value.selection.active
  -- Horizontal auto-scroll: clamp, then bring the caret into the window.
  let maxScroll := max 0 (textW + caretW - innerW)
  let mut s := min (max 0 (← vis.scroll.get)) maxScroll
  if caretX - s > innerW - caretW then s := caretX - (innerW - caretW)
  if caretX - s < 0 then s := caretX
  vis.scroll.set s
  -- Clipped, scrolled text stack: selection under glyphs under underline
  -- under caret.
  DrawScope.clipRect ⟨pad, labelSpace, pad + innerW, labelSpace + boxH⟩ <|
    DrawScope.translate ⟨pad - s, textTop⟩ do
      let sel := vis.value.selection
      if vis.focused && vis.enabled && !sel.collapsed then
        let x0 ← xAt sel.start
        let x1 ← xAt sel.«end»
        DrawScope.drawRect (.solid vis.selectionColor) ⟨x0, 0⟩ ⟨x1 - x0, lineH⟩
      if vis.value.text.isEmpty then
        -- Placeholder while empty (suppressed under a resting label).
        if vis.hasLabel == false || vis.labelProgress > 0.9 then
          if let some ph := vis.placeholder? then ph.draw ⟨0, 0⟩
      else
        vis.layout.draw ⟨0, 0⟩
      if let some comp := vis.value.composition then
        let x0 ← xAt comp.start
        let x1 ← xAt comp.«end»
        DrawScope.drawRect (.solid vis.textColor) ⟨x0, lineH - px 1⟩ ⟨x1 - x0, px 1⟩
      if vis.focused && vis.enabled && vis.caretOn then
        DrawScope.drawRect (.solid vis.caretColor) ⟨caretX, 0⟩ ⟨caretW, lineH⟩
  -- Label float: one label continuously morphing font size *and* position
  -- between the resting text band (p = 0) and the floating top strip (p = 1),
  -- driven by `labelProgress` (Compose animates the label's textStyle, not a
  -- crossfade of two pre-laid layouts).
  if vis.hasLabel then
    if let some lbl := vis.label? then
      lbl.draw ⟨pad, (1 - vis.labelProgress) * textTop⟩
  -- IME: publish the caret area (window coordinates) when it moved.
  if vis.focused && vis.enabled then
    if let some w := vis.window? then
      let scale := if ctx.density.density > 0 then ctx.density.density else 1
      let toWin (v : Float32) : Int32 := (v / scale).floor.toInt32
      let base := ctx.translation
      let area := (toWin base.x, toWin (base.y + labelSpace),
                   toWin sz.width, toWin boxH,
                   toWin (base.x + pad - s + caretX))
      unless (← vis.lastImeArea.get) == some area do
        vis.lastImeArea.set (some area)
        let (ax, ay, aw, ah, acur) := area
        w.window.setTextInputArea (some ⟨ax, ay, aw, ah⟩) (acur - ax)
      -- App→IME sync: whenever the (text, selection) the IME should believe
      -- changed — a tapped caret, a programmatic edit, or an IME edit echoed
      -- back — push it through the platform hook (the receiving side diffs
      -- against its mirror, so echoes are cheap no-ops). UTF-16 units, the
      -- offsets `InputMethodManager.updateSelection` speaks.
      let state := (vis.value.text, vis.value.selection)
      unless (← vis.lastImeSync.get) == some state do
        vis.lastImeSync.set (some state)
        if let some h ← w.imeSyncHook.get then
          let t := vis.value.text
          h.sync t (Utf8.utf16Offset t vis.value.selection.start).toUInt32
            (Utf8.utf16Offset t vis.value.selection.«end»).toUInt32
  -- Selection chrome: publish this frame's anchor geometry (window px) for
  -- the chrome popups composed next frame — the `onGloballyPositioned`
  -- contract. The cell's equality skip makes the steady state free.
  let sel := vis.value.selection
  if vis.chromeOn && vis.focused && vis.enabled && !sel.collapsed then
    let base := ctx.translation
    let x0 ← xAt sel.start
    let x1 ← xAt sel.«end»
    -- The visible clip = the field's inner text span ∩ the ambient draw
    -- clip (an enclosing scroll viewport) — chrome scrolled out of view is
    -- suppressed instead of floating over neighboring content.
    let (acL, acT, acR, acB) := match ctx.clip with
      | some c => (c.left, c.top, c.right, c.bottom)
      | none => (-1e30, -1e30, 1e30, 1e30)
    vis.chromeAnchors.set (some
      { startX := base.x + pad - s + x0
        endX := base.x + pad - s + x1
        lineTop := base.y + textTop
        lineBottom := base.y + textTop + lineH
        clipLeft := max (base.x + pad) acL
        clipRight := min (base.x + pad + innerW) acR
        clipTop := acT
        clipBottom := acB })
    -- Movement flag: the handles track a scrolling field per frame
    -- (Android's native behavior); only the toolbar sits the motion out,
    -- returning when the position holds still for a frame.
    let pos := (base.x, base.y)
    let moved := match ← vis.chromePos.get with
      | some p => p != pos
      | none => false
    vis.chromeMoving.set moved
    vis.chromePos.set (some pos)
  else
    vis.chromeAnchors.set none
    vis.chromeMoving.set false
    vis.chromePos.set none

/-! ## The composable -/

/-- The full-state Material-outlined single-line text field (see the module
docstring for the full behavior): `value` carries text *plus*
selection/composition. **Controlled**: `value` is the single source of
truth; every edit (typing, motion, selection, IME) is reported through
`onValueChange` and takes effect when the caller echoes it back. Most apps
want the plain-`String` `TextField` instead. Mirrors
`androidx.compose.material3.OutlinedTextField` (the `TextFieldValue`
overload).

Only `singleLine := true` is supported (the default; the flag controls
newline stripping and exists for API fidelity).

`minWidth` (default 280 dp, matching M3's `TextFieldDefaults.MinWidth`) is the
field's minimum measured width; it is clamped to the incoming max constraint,
so the field never forces its parent to overflow. -/
composable def ValueTextField (value : TextFieldValue)
    (onValueChange : TextFieldValue → IO Unit) (modifier : Modifier := {})
    (enabled : Bool := true) (isError : Bool := false)
    (placeholder : String := "") (label : Option String := none)
    (textStyle : TextStyle := {}) (minWidth : Dp := 280)
    (singleLine : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shape := (← MaterialTheme.shapes).extraSmall
  let ambient ← LocalTextStyle.current
  let density ← LocalDensity.current
  let window? ← LocalWindowContext.current
  let tc? ← LocalTextContext.current
  -- Semantics: an editable text node — findable by role/label, its current
  -- value asserted through `editableText` (Compose's `EditableText` +
  -- `Disabled` + label `Text` properties).
  let modifier := modifier.semantics (role := some .textField)
    (editableText := some value.text) (text := label) (disabled := some !enabled)
  match tc? with
  | none =>
    -- Composed outside a window (no text stack): occupy no space.
    Layout modifier .leaf (policyInputs := some 0)
  | some tc =>
    -- Remembered state.
    let focusedState ← remember (mutableStateOf false)
    let focused ← focusedState.get
    let valueRef ← remember (IO.mkRef value)
    -- Re-synchronize the optimistic ref with the authoritative prop.
    valueRef.set value.normalized
    let onChangeRef ← rememberUpdatedRef onValueChange
    let scrollRef ← remember (IO.mkRef (0.0 : Float32))
    let lastImeArea ← remember
      (IO.mkRef (none : Option (Int32 × Int32 × Int32 × Int32 × Int32)))
    let lastImeSync ← remember
      (IO.mkRef (none : Option (String × TextRange)))
    -- Touch selection chrome: visibility reducer state, the draw-pass anchor
    -- cell, and the grabbed-handle role (crossing swaps it mid-drag).
    let chrome ← remember (mutableStateOf ({} : ChromeState))
    let chromeAnchors ← remember (mutableStateOf (none : Option ChromeAnchors))
    let chromeMoving ← remember (mutableStateOf false)
    let chromePos ← remember (IO.mkRef (none : Option (Float32 × Float32)))
    let dragHandleRef ← remember (IO.mkRef SelectionHandle.start)
    let chromeStep (ev : ChromeEvent) : IO Unit := chrome.modify (·.step ev)
    let cs ← chrome.get
    let cellText ← remember (IO.mkRef (none : Option TextLayout))
    let cellPlaceholder ← remember (IO.mkRef (none : Option TextLayout))
    let cellLabel ← remember (IO.mkRef (none : Option TextLayout))
    -- Colors and styles.
    let textColor := if enabled then colors.onSurface
                     else colors.onSurface.withAlpha disabledContentAlpha
    let outlineColor :=
      if !enabled then colors.onSurface.withAlpha disabledContainerAlpha
      else if isError then colors.error
      else if focused then colors.primary
      else colors.outline
    let outlineWidth : Dp := if focused && enabled then 2 else 1
    let caretColor := if isError then colors.error else colors.primary
    let labelColor :=
      if !enabled then colors.onSurface.withAlpha disabledContentAlpha
      else if isError then colors.error
      else if focused then colors.primary
      else colors.onSurfaceVariant
    let resolvedStyle := { ambient.merge textStyle with color := textColor }
    let layout ← obtainFieldLayout cellText tc value.text resolvedStyle density
    let placeholder? ← if placeholder.isEmpty then pure none else do
      let style := { resolvedStyle with
                     color := if enabled then colors.onSurfaceVariant else textColor }
      pure (some (← obtainFieldLayout cellPlaceholder tc placeholder style density))
    -- Label float progress (0 = resting in the text band, 1 = floated up).
    let floating := focused || !value.text.isEmpty
    let labelProgress ← (← animateFloatAsState (if floating then 1 else 0)
      (.tween 150 0 .fastOutSlowIn)).get
    -- One label, laid out at the interpolated font size between the resting
    -- text size and the 11 sp floating size — draws continuously, no crossfade.
    let label? ← match label with
      | none => pure none
      | some l => do
        let restSp := resolvedStyle.fontSize.value
        let lblSize : Sp := ⟨restSp + (11 - restSp) * labelProgress⟩
        let style := { resolvedStyle with fontSize := lblSize, color := labelColor }
        pure (some (← obtainFieldLayout cellLabel tc l style density))
    -- Edit application: optimistic ref first (so back-to-back events between
    -- recompositions compose), then the controlled callback.
    let sanitize (t : String) : String := if singleLine then stripNewlines t else t
    let doEdit (cmd : EditCommand) : IO Unit := do
      let v ← valueRef.get
      let v' := v.apply cmd
      unless v' == v do
        valueRef.set v'
        chromeStep (if v'.text == v.text
                    then .selectionChanged v'.selection.collapsed
                    else .textEdited)
        (← onChangeRef.get) v'
    let doCopy : IO Unit := do
      let t := (← valueRef.get).selectedText
      unless t.isEmpty do Sdl.setClipboardText t
    let doPaste : IO Unit := do
      let t := sanitize (← Sdl.getClipboardText)
      unless t.isEmpty do doEdit (.insert t)
    let onKey (ke : KeyEvent) : IO Bool := do
      if !enabled then return false
      -- Esc / the platform back action dismiss the selection chrome —
      -- consumed only while chrome is up, so both keys keep their normal
      -- routing otherwise.
      if ke.down && !ke.isRepeat && (ke.key == .escape || ke.key == .acBack) then
        if (← chrome.get).shown then
          chromeStep .dismissKey
          return true
      match textFieldKeyAction ke with
      | none => return false
      | some (.edit cmd) => doEdit cmd; return true
      | some .copy => doCopy; return true
      | some .cut => doCopy; doEdit .deleteSelection; return true
      | some .paste => doPaste; return true
    let onText (t : String) : IO Bool := do
      if !enabled then return false
      doEdit (.insert (sanitize t))
      return true
    let onEditing (t : String) (start _length : Int32) : IO Bool := do
      if !enabled then return false
      let t := sanitize t
      let cursor := if start < 0 then t.utf8ByteSize
                    else Utf8.codepointToByte t start.toNatClampNeg
      doEdit (.setComposition t cursor)
      return true
    -- Mouse hit → caret byte offset (nearest boundary, scroll compensated).
    let hitCaret (pos : Offset) : IO Nat := do
      let v ← valueRef.get
      if v.text.isEmpty then return 0
      let tsz ← layout.measure none
      let tx := pos.x - density.dpToPx contentPadDp + (← scrollRef.get)
      if tx ≤ 0 then return 0
      if tx ≥ tsz.width.toFloat32 then return v.text.utf8ByteSize
      let off ← layout.hitToByteOffset ⟨tx, tsz.height.toFloat32 / 2⟩
      let r ← layout.byteOffsetToRect off
      return if tx > (r.left + r.right) / 2 then Utf8.next v.text off else off
    -- `focused` here is the pre-tap composition snapshot: on the tap that
    -- GAINS focus the router's commit precedes this handler but the
    -- recomposition has not run yet, so this stays false and the focus
    -- hook's own StartTextInput is not disturbed (bouncing it would
    -- restart the fresh IME session).
    let reshowKeyboard : IO Unit := do
      if focused && enabled then
        if let some w := window? then
          w.window.stopTextInput
          w.window.startTextInput
    let selectWord (pos : Offset) : IO TextRange := do
      doEdit (.selectWord (← hitCaret pos))
      return (← valueRef.get).selection
    -- Handle drag: map the finger's window x back into the element through
    -- the field's *true* window origin (`chromePos`, recorded by the draw
    -- pass while chrome is up; `hitCaret` re-adds pad and scroll), run the
    -- pure drag math, keep the grabbed role across crossings. NOT via the
    -- published `clipLeft`: that edge is intersected with the ambient clip,
    -- so an enclosing container cutting the field's left edge would offset
    -- every drag by the cut amount. The dragged end is `active`, so the
    -- field's caret auto-scroll follows the finger for free.
    let handleGrab (h : SelectionHandle) : IO Unit := do
      dragHandleRef.set h
      chromeStep (.handleGrab h)
    let handleDragTo (winX : Float32) : IO Unit := do
      if let some (baseX, _) ← chromePos.get then
        let off ← hitCaret ⟨winX - baseX, 0⟩
        let v ← valueRef.get
        let (sel', h') := (← dragHandleRef.get).dragSelection v.text v.selection off
        dragHandleRef.set h'
        doEdit (.setSelection sel')
    let handleRelease : IO Unit := chromeStep .handleRelease
    let gestureParams ← rememberUpdatedRef
      ({ enabled, hitCaret, edit := doEdit, reshowKeyboard, selectWord
         chromeShow := chromeStep .touchSelected
         chromeSettle := chromeStep .settled }
        : FieldGestureParams)
    -- Caret blink: composed only while focused, so an idle field schedules
    -- no frame work.
    let caretOn ← if focused && enabled then do
        let it ← rememberInfiniteTransition
        let phase ← it.animateFloat 0 1 (.infiniteRepeatable (.tween 1000 0 .linear))
        pure (((← phase.get) < 0.5 : Bool))
      else
        pure false
    let vis : FieldVisuals :=
      { layout, placeholder?, label?
        value := value.normalized, focused, enabled, caretOn
        labelProgress
        outlineColor, outlineWidth, caretColor
        selectionColor := colors.primary.withAlpha 0.40
        textColor, shape, hasLabel := label.isSome
        scroll := scrollRef, window?, lastImeArea, lastImeSync
        chromeOn := cs.shown, chromeAnchors, chromeMoving, chromePos }
    let hasLabel := label.isSome
    let policy : MeasurePolicy := fun scope _ c => do
      let d := scope.density
      let lineH ← layout.lineHeight
      let labelSpace := if hasLabel then d.dpRoundToPx labelStripDp else 0
      let boxH := max (d.dpRoundToPx 40) (lineH + d.dpRoundToPx 16)
      -- Clamp the desired min-width to the incoming max so the field never
      -- forces its parent to overflow (a hard-coded 280 dp min once collapsed
      -- a demo's Row to zero height).
      let wantW := d.dpRoundToPx minWidth
      let w := if c.hasBoundedWidth then min wantW c.maxWidth else wantW
      return { size := c.constrain ⟨w, boxH + labelSpace⟩ }
    let m := modifier
      |>.then (if enabled then Modifier.pointerHoverIcon .text else {})
      |>.focusable enabled
      |>.onFocusChanged (fun f => do
          focusedState.set f
          unless f do chromeStep .focusLost)
      |>.onKeyEvent onKey
      |>.onTextInput onText
      |>.onTextEditing onEditing
      |>.pointerInput
          (mixKeys (stringKey "Compose.Material.TextField") (if enabled then 1 else 0))
          (fieldGesture gestureParams)
      |>.drawBehind (drawTextField vis)
    Layout m policy
      (policyInputs := some
        (mixKeys minWidth.value.toBits.toUInt64
          (mixKeys (resolvedStyle.fontSize.value.toBits.toUInt64)
            (mixKeys (match resolvedStyle.lineHeight with
                      | none => 0
                      | some sp => mixKeys 0x11 sp.value.toBits.toUInt64)
              (mixKeys density.density.toBits.toUInt64 (if hasLabel then 1 else 0))))))
    -- Touch selection chrome: the handles, as non-dismissable popups over
    -- the geometry the draw pass published (one frame behind the pixels —
    -- the `onGloballyPositioned` contract, imperceptible at device rates).
    -- A handle scrolled outside the inner clip window gets no anchor and is
    -- not composed.
    if cs.shown && focused && enabled then
      if let some a ← chromeAnchors.get then
        if let some r := a.handleAnchor .start then
          selectionHandle .start r colors.primary
            (handleGrab .start) handleDragTo handleRelease
        if let some r := a.handleAnchor .«end» then
          selectionHandle .«end» r colors.primary
            (handleGrab .«end») handleDragTo handleRelease
        -- The toolbar (hidden while a handle drag is in flight, while the
        -- field is moving under an enclosing scroll, and while the line is
        -- out of the viewport; composed after the handles so it hit-tests
        -- first where they overlap). Copy collapses the selection
        -- (Android's deselect-after-copy); every action hides the chrome
        -- through the reducer.
        if cs.toolbar && cs.dragging.isNone && !(← chromeMoving.get)
            && a.lineVisible then
          let canPaste ← liftM (m := IO) Sdl.hasClipboardText
          TextFieldToolbar (a.toolbarAnchor (density.dpToPx chromeHandleTouch))
            canPaste
            (onCut := do doCopy; doEdit .deleteSelection)
            (onCopy := do
              doCopy
              doEdit (.setSelection (.caret (← valueRef.get).selection.«end»)))
            (onPaste := doPaste)

/-- The Material-outlined single-line text field over plain `String` state:
remembers selection/composition internally and reports plain strings — what
most apps want (use `ValueTextField` for full selection/composition
control). An external `value` change (the app rewriting the text) resets the
caret to the nearest boundary at or before its old position. Mirrors the
`String` overload of `androidx.compose.material3.OutlinedTextField`. -/
composable def TextField (value : String) (onValueChange : String → IO Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) (isError : Bool := false)
    (placeholder : String := "") (label : Option String := none)
    (textStyle : TextStyle := {}) (minWidth : Dp := 280) : Composable Unit := do
  let internal ← remember (mutableStateOf
    ({ text := value, selection := .caret value.utf8ByteSize } : TextFieldValue))
  let cur ← internal.get
  let v := if cur.text == value then cur
           else ({ text := value, selection := .caret cur.selection.active
                   composition := none } : TextFieldValue).normalized
  ValueTextField v
    (onValueChange := fun v' => do
      let prev ← internal.get
      internal.set v'
      unless v'.text == prev.text do onValueChange v'.text)
    (modifier := modifier) (enabled := enabled) (isError := isError)
    (placeholder := placeholder) (label := label) (textStyle := textStyle)
    (minWidth := minWidth)

end Compose

end
