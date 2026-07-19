module

public import Compose.Ui.Text.EditModel
public meta import Compose.Ui.Text.EditModel
public import Compose.Core.Geometry
public meta import Compose.Core.Geometry
public import Compose.Core.Density
public meta import Compose.Core.Density

public section

namespace Compose

/-!
# Text selection chrome (`Compose/Material/TextFieldChrome.lean`)

The pure core of `TextField`'s touch selection chrome — the floating
selection handles and the Cut/Copy/Paste toolbar that appear over a
finger long-press selection (Android convention; mouse and keyboard
selection never show chrome).

Everything here is presentation-side and pure:

* `SelectionHandle.dragSelection` — how dragging a handle moves the
  selection (character granularity, the dragged end becomes `active`,
  crossing the fixed end swaps handle roles, and the selection never
  collapses below one codepoint — Android's selection-handle rules).
* `ChromeState.step` — the visibility reducer. Chrome is **not** part of
  the editing model: the selection itself persists when chrome hides;
  only what is drawn changes. Tap-elsewhere dismissal deliberately does
  not use the overlay dismiss scrim (that would swallow the tap — Android
  replays it), so every hide path is an explicit `ChromeEvent`.
* `ChromeAnchors` + placement — window-px anchor math from the geometry
  the field's draw pass publishes each frame (caret x of both selection
  ends, the text line extent, and the inner clip window). A handle whose
  x scrolled outside the clip window gets no anchor (not composed).

Single-line LTR only, like the field itself (no bidi anywhere in the
text stack).
-/

/-- Which selection handle: the one at `TextRange.start` or the one at
`TextRange.end`. Roles are positional — a drag crossing the fixed end
swaps them (`dragSelection`). -/
inductive SelectionHandle where
  | start
  | «end»
  deriving BEq, Repr, Inhabited

/-- Drag handle `h` of selection `sel` (over `text`) to boundary-snapped
byte offset `off`: the other end stays fixed, the dragged end becomes the
range's `active` (so the field's caret auto-scroll follows the finger),
crossing the fixed end swaps which handle is grabbed, and the selection is
clamped to keep at least one codepoint (dragging a handle can never
collapse the selection — Android's selection-handle rule). Returns the new
selection and the handle role now grabbed. -/
def SelectionHandle.dragSelection (h : SelectionHandle) (text : String)
    (sel : TextRange) (off : Nat) : TextRange × SelectionHandle :=
  let fixed := match h with
    | .start => sel.«end»
    | .«end» => sel.start
  if off < fixed then (⟨fixed, off⟩, .start)
  else if off > fixed then (⟨fixed, off⟩, .«end»)
  else match h with
    | .start => (⟨fixed, Utf8.prev text fixed⟩, .start)
    | .«end» => (⟨fixed, Utf8.next text fixed⟩, .«end»)

-- extend / shrink on the same side ("hello world": all 1-byte)
#guard SelectionHandle.«end».dragSelection "hello world" ⟨0, 5⟩ 8
        == (⟨0, 8⟩, .«end»)
#guard SelectionHandle.«end».dragSelection "hello world" ⟨0, 5⟩ 3
        == (⟨0, 3⟩, .«end»)
#guard SelectionHandle.start.dragSelection "hello world" ⟨6, 11⟩ 0
        == (⟨11, 0⟩, .start)
-- the dragged end is `active`; the fixed end is `anchor`
#guard (SelectionHandle.start.dragSelection "hello world" ⟨6, 11⟩ 2).1.active == 2
-- crossing swaps the grabbed role
#guard SelectionHandle.start.dragSelection "hello world" ⟨0, 5⟩ 8
        == (⟨5, 8⟩, .«end»)
#guard SelectionHandle.«end».dragSelection "hello world" ⟨2, 5⟩ 0
        == (⟨2, 0⟩, .start)
-- collapse clamp: one codepoint stays selected
#guard SelectionHandle.«end».dragSelection "hello world" ⟨0, 5⟩ 0
        == (⟨0, 1⟩, .«end»)
#guard SelectionHandle.start.dragSelection "hello world" ⟨0, 5⟩ 5
        == (⟨5, 4⟩, .start)
-- multibyte clamp steps whole codepoints ("héllo": é is 2 bytes at 1..3)
#guard SelectionHandle.«end».dragSelection "héllo" ⟨1, 4⟩ 1 == (⟨1, 3⟩, .«end»)
#guard SelectionHandle.start.dragSelection "héllo" ⟨0, 3⟩ 3 == (⟨3, 1⟩, .start)

/-- Visibility state of the selection chrome. Presentation-only — the
selection in the editing model is never touched by hiding chrome. -/
structure ChromeState where
  /-- Handles are visible. -/
  shown : Bool := false
  /-- The toolbar is visible (implies `shown`; hidden mid-drag). -/
  toolbar : Bool := false
  /-- The handle currently being dragged, if any. -/
  dragging : Option SelectionHandle := none
  deriving BEq, Repr, Inhabited

/-- What happened, as far as chrome visibility is concerned. -/
inductive ChromeEvent where
  /-- A finger long-press selected a word (the selection drag may follow). -/
  | touchSelected
  /-- The selecting finger lifted — the selection settled. -/
  | settled
  /-- A finger grabbed a handle. -/
  | handleGrab (h : SelectionHandle)
  /-- The handle drag ended. -/
  | handleRelease
  /-- The selection changed by other means (caret tap, keyboard). -/
  | selectionChanged (collapsed : Bool)
  /-- The text changed (typing, IME, cut, paste). -/
  | textEdited
  /-- The field lost focus. -/
  | focusLost
  /-- The field's window rect moved with the selection unchanged (an
  enclosing container scrolled). -/
  | fieldMoved
  /-- Esc / the platform back action. -/
  | dismissKey

/-- The chrome visibility reducer: long-press shows handles, the settling
release adds the toolbar, a handle grab hides the toolbar for the duration
of the drag, and every editing/focus/movement/dismiss event hides the
whole chrome (selection untouched). -/
def ChromeState.step (s : ChromeState) : ChromeEvent → ChromeState
  | .touchSelected => { shown := true }
  | .settled => if s.shown then { shown := true, toolbar := true } else s
  | .handleGrab h => { shown := true, dragging := some h }
  | .handleRelease => { shown := true, toolbar := true }
  | .selectionChanged collapsed => if collapsed then {} else s
  | .textEdited => {}
  | .focusLost => {}
  | .fieldMoved => {}
  | .dismissKey => {}

-- the long-press → settle → grab → release lifecycle
#guard ChromeState.step {} .touchSelected == { shown := true }
#guard ChromeState.step { shown := true } .settled
        == { shown := true, toolbar := true }
#guard ChromeState.step {} .settled == {}                      -- stray settle
#guard ChromeState.step { shown := true, toolbar := true } (.handleGrab .«end»)
        == { shown := true, dragging := some .«end» }
#guard ChromeState.step { shown := true, dragging := some .start } .handleRelease
        == { shown := true, toolbar := true }
-- hide paths (selection persists — chrome only)
#guard ChromeState.step { shown := true, toolbar := true } .textEdited == {}
#guard ChromeState.step { shown := true, toolbar := true } .focusLost == {}
#guard ChromeState.step { shown := true, toolbar := true } .fieldMoved == {}
#guard ChromeState.step { shown := true, toolbar := true } .dismissKey == {}
#guard ChromeState.step { shown := true, toolbar := true } (.selectionChanged true)
        == {}
#guard ChromeState.step { shown := true, toolbar := true } (.selectionChanged false)
        == { shown := true, toolbar := true }

/-- Chrome geometry for one frame, published by the field's draw pass, all
in window px: the caret x of both selection ends, the text line's vertical
extent, and the inner clip window (the visible text span — offsets outside
it are horizontally scrolled out of view). -/
structure ChromeAnchors where
  /-- Window-px caret x at `selection.start`. -/
  startX : Float32
  /-- Window-px caret x at `selection.end`. -/
  endX : Float32
  /-- Window-px top of the text line. -/
  lineTop : Float32
  /-- Window-px bottom of the text line (handles hang from here). -/
  lineBottom : Float32
  /-- Window-px left edge of the visible text span. -/
  clipLeft : Float32
  /-- Window-px right edge of the visible text span. -/
  clipRight : Float32
  deriving Repr, BEq, Inhabited

/-- The popup anchor for handle `h`: a point rect at its caret x on the
line bottom, or `none` when that end is horizontally scrolled outside the
visible text span (the handle is not composed). -/
def ChromeAnchors.handleAnchor (a : ChromeAnchors) (h : SelectionHandle) :
    Option Rect :=
  let x := match h with | .start => a.startX | .«end» => a.endX
  if x < a.clipLeft || x > a.clipRight then none
  else some ⟨x, a.lineBottom, x, a.lineBottom⟩

#guard ChromeAnchors.handleAnchor ⟨40, 90, 10, 30, 20, 100⟩ .start
        == some ⟨40, 30, 40, 30⟩
#guard ChromeAnchors.handleAnchor ⟨40, 90, 10, 30, 20, 100⟩ .«end»
        == some ⟨90, 30, 90, 30⟩
-- scrolled out of the clip window: no anchor
#guard ChromeAnchors.handleAnchor ⟨10, 90, 10, 30, 20, 100⟩ .start == none
#guard ChromeAnchors.handleAnchor ⟨40, 120, 10, 30, 20, 100⟩ .«end» == none
-- exactly on the clip edge still shows
#guard ChromeAnchors.handleAnchor ⟨20, 100, 10, 30, 20, 100⟩ .start
        == some ⟨20, 30, 20, 30⟩

/-- The toolbar's anchor: the visible part of the selection's line-span
rect (ends clamped into the clip window). The toolbar popup hangs above it
(`Popup (preferAbove := true)`), falling back below when out of room. -/
def ChromeAnchors.toolbarAnchor (a : ChromeAnchors) : Rect :=
  ⟨max a.startX a.clipLeft, a.lineTop, min a.endX a.clipRight, a.lineBottom⟩

#guard ChromeAnchors.toolbarAnchor ⟨40, 90, 10, 30, 20, 100⟩ == ⟨40, 10, 90, 30⟩
-- both ends scrolled out: clamped to the visible span
#guard ChromeAnchors.toolbarAnchor ⟨10, 120, 10, 30, 20, 100⟩ == ⟨20, 10, 100, 30⟩

/-! ## Chrome metrics (dp) -/

/-- Handle glyph size (the teardrop's bounding square). -/
def chromeHandleSize : Dp := 24

/-- Handle touch-target size (the hit box centered on the glyph). -/
def chromeHandleTouch : Dp := 32

/-- Fixed toolbar button width — fixed so tests can compute tap targets. -/
def chromeToolbarButtonWidth : Dp := 64

/-- Gap between the selection line and the toolbar. -/
def chromeToolbarGap : Dp := 8

end Compose

end
