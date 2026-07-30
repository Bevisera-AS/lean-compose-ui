module

public import Compose.Ui.Text.EditModel
public meta import Compose.Ui.Text.EditModel
public import Compose.Core.Geometry
public meta import Compose.Core.Geometry
public import Compose.Core.Density
public meta import Compose.Core.Density
public import Compose.Ui.Overlay
public meta import Compose.Ui.Overlay
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout
public import Compose.Material.Surface
public meta import Compose.Material.Surface
public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Foundation.Gestures
public meta import Compose.Foundation.Gestures

public section

namespace Compose

open Draw

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

/-- What happened, as far as chrome visibility is concerned. Container
scroll is deliberately NOT an event: chrome *tracks* a moving field
(Android's native handles follow the text through a scroll) — the draw
pass republishes anchors per frame and flags motion separately so only
the toolbar sits out the movement. -/
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
  /-- Esc / the platform back action. -/
  | dismissKey

/-- The chrome visibility reducer: long-press shows handles, the settling
release adds the toolbar, a handle grab hides the toolbar for the duration
of the drag, and every editing/focus/dismiss event hides the whole chrome
(selection untouched). -/
def ChromeState.step (s : ChromeState) : ChromeEvent → ChromeState
  | .touchSelected => { shown := true }
  | .settled => if s.shown then { shown := true, toolbar := true } else s
  | .handleGrab h => { shown := true, dragging := some h }
  | .handleRelease => { shown := true, toolbar := true }
  | .selectionChanged collapsed => if collapsed then {} else s
  | .textEdited => {}
  | .focusLost => {}
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
#guard ChromeState.step { shown := true, toolbar := true } .dismissKey == {}
#guard ChromeState.step { shown := true, toolbar := true } (.selectionChanged true)
        == {}
#guard ChromeState.step { shown := true, toolbar := true } (.selectionChanged false)
        == { shown := true, toolbar := true }

/-- Chrome geometry for one frame, published by the field's draw pass, all
in window px: the caret x of both selection ends, the text line's vertical
extent, and the visible clip — the field's inner text span intersected
with the ambient draw clip (an enclosing scroll viewport), so chrome
scrolled out of view is suppressed rather than floating over neighboring
content. -/
structure ChromeAnchors where
  /-- Window-px caret x at `selection.start`. -/
  startX : Float32
  /-- Window-px caret x at `selection.end`. -/
  endX : Float32
  /-- Window-px top of the text line. -/
  lineTop : Float32
  /-- Window-px bottom of the text line (handles hang from here). -/
  lineBottom : Float32
  /-- Window-px left edge of the visible text span (∩ ambient clip). -/
  clipLeft : Float32
  /-- Window-px right edge of the visible text span (∩ ambient clip). -/
  clipRight : Float32
  /-- Window-px top of the ambient clip (enclosing scroll viewport). -/
  clipTop : Float32 := -1e30
  /-- Window-px bottom of the ambient clip. -/
  clipBottom : Float32 := 1e30
  deriving Repr, BEq, Inhabited

/-- The popup anchor for handle `h`: a point rect at its caret x on the
line bottom, or `none` when that end is scrolled outside the visible clip
— horizontally out of the text span, or vertically out of the enclosing
viewport (the handle is not composed). -/
def ChromeAnchors.handleAnchor (a : ChromeAnchors) (h : SelectionHandle) :
    Option Rect :=
  let x := match h with | .start => a.startX | .«end» => a.endX
  if x < a.clipLeft || x > a.clipRight
     || a.lineBottom < a.clipTop || a.lineBottom > a.clipBottom then none
  else some ⟨x, a.lineBottom, x, a.lineBottom⟩

/-- Whether any of the selection's line is inside the visible clip — the
toolbar's composition gate (an off-viewport selection shows no toolbar). -/
def ChromeAnchors.lineVisible (a : ChromeAnchors) : Bool :=
  a.clipLeft ≤ a.clipRight
    && a.lineBottom ≥ a.clipTop && a.lineTop ≤ a.clipBottom

#guard ChromeAnchors.handleAnchor ⟨40, 90, 10, 30, 20, 100, 0, 160⟩ .start
        == some ⟨40, 30, 40, 30⟩
#guard ChromeAnchors.handleAnchor ⟨40, 90, 10, 30, 20, 100, 0, 160⟩ .«end»
        == some ⟨90, 30, 90, 30⟩
-- scrolled out of the clip window: no anchor
#guard ChromeAnchors.handleAnchor ⟨10, 90, 10, 30, 20, 100, 0, 160⟩ .start == none
#guard ChromeAnchors.handleAnchor ⟨40, 120, 10, 30, 20, 100, 0, 160⟩ .«end» == none
-- exactly on the clip edge still shows
#guard ChromeAnchors.handleAnchor ⟨20, 100, 10, 30, 20, 100, 0, 160⟩ .start
        == some ⟨20, 30, 20, 30⟩
-- the line scrolled above / below the viewport: no anchor
#guard ChromeAnchors.handleAnchor ⟨40, 90, -30, -10, 20, 100, 0, 160⟩ .start == none
#guard ChromeAnchors.handleAnchor ⟨40, 90, 170, 190, 20, 100, 0, 160⟩ .«end» == none
-- line visibility (the toolbar gate)
#guard ChromeAnchors.lineVisible ⟨40, 90, 10, 30, 20, 100, 0, 160⟩
#guard !ChromeAnchors.lineVisible ⟨40, 90, -30, -10, 20, 100, 0, 160⟩
#guard !ChromeAnchors.lineVisible ⟨40, 90, 170, 190, 20, 100, 0, 160⟩
-- horizontally empty visible span (field scrolled out sideways)
#guard !ChromeAnchors.lineVisible ⟨40, 90, 10, 30, 120, 100, 0, 160⟩

/-- The toolbar's anchor: the visible part of the selection's line-span
rect (ends clamped into the clip window), its bottom pushed down by
`handleClearance` (the handle touch-box height) so the below-fallback
placement clears the handles hanging off the line. The toolbar popup
prefers the space above it (`Popup (preferAbove := true)`, from the
unmoved line top), falling back below when out of room. -/
def ChromeAnchors.toolbarAnchor (a : ChromeAnchors)
    (handleClearance : Float32 := 0) : Rect :=
  ⟨max a.startX a.clipLeft, a.lineTop, min a.endX a.clipRight,
   a.lineBottom + handleClearance⟩

#guard ChromeAnchors.toolbarAnchor ⟨40, 90, 10, 30, 20, 100, 0, 160⟩
        == ⟨40, 10, 90, 30⟩
-- the handle clearance drops only the bottom (the below-fallback edge)
#guard ChromeAnchors.toolbarAnchor ⟨40, 90, 10, 30, 20, 100, 0, 160⟩ 32
        == ⟨40, 10, 90, 62⟩
-- both ends scrolled out: clamped to the visible span
#guard ChromeAnchors.toolbarAnchor ⟨10, 120, 10, 30, 20, 100, 0, 160⟩
        == ⟨20, 10, 100, 30⟩

/-! ## Chrome metrics (dp) -/

/-- Handle glyph size (the teardrop's bounding square). -/
def chromeHandleSize : Dp := 24

/-- Handle touch-target size (the hit box centered on the glyph). -/
def chromeHandleTouch : Dp := 32

/-- Fixed toolbar button width — fixed so tests can compute tap targets. -/
def chromeToolbarButtonWidth : Dp := 64

/-- Toolbar button (and so toolbar) height. -/
def chromeToolbarHeight : Dp := 40

/-- Gap between the selection line and the toolbar. -/
def chromeToolbarGap : Dp := 8

/-! ## The chrome composables -/

/-- The teardrop handle glyph: a filled circle with the corner toward the
anchored caret squared off — the end handle's tip is its top-left corner,
the start handle's its top-right (Android's mirrored pair). Drawn flush to
the top of the touch box, on the tip's side. -/
private def drawHandleGlyph (h : SelectionHandle) (color : Color) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  let r := ctx.density.dpToPx chromeHandleSize / 2
  match h with
  | .«end» =>
    DrawScope.drawRect (.solid color) ⟨0, 0⟩ ⟨r, r⟩
    DrawScope.drawCircle (.solid color) ⟨r, r⟩ r
  | .start =>
    DrawScope.drawRect (.solid color) ⟨sz.width - r, 0⟩ ⟨r, r⟩
    DrawScope.drawCircle (.solid color) ⟨sz.width - r, r⟩ r

/-- The handle drag gesture: the press is consumed immediately (the popup
is hit-tested before the app content, and capture then routes every move
here — an enclosing scrollable can never steal a handle drag), each move
reports the finger's window x, release or cancel settles. Callbacks live
in a ref so the long-lived coroutine always sees the latest composition's
closures (the `fieldGesture` idiom). -/
private partial def handleDragLoop
    (cb : IO.Ref (IO Unit × (Float32 → IO Unit) × IO Unit))
    (box : IO.Ref Rect) (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press then
    ev.consume
    (← cb.get).1
    drag ev.pointerId
  handleDragLoop cb box scope
where
  drag (pid : UInt64) : UiTask Unit := do
    let ev ← scope.awaitEvent
    if ev.pointerId != pid then drag pid else
    match ev.eventType with
    | .move =>
      ev.consume
      (← cb.get).2.1 ((← box.get).left + ev.position.x)
      drag pid
    | .release => ev.consume; (← cb.get).2.2
    | .exit => (← cb.get).2.2
    | _ => drag pid

/-- One floating selection handle: a non-dismissable popup hanging from
`anchor` (the caret point on the text line's bottom — see
`ChromeAnchors.handleAnchor`), hosting the teardrop glyph in a
`chromeHandleTouch` touch box whose tip corner aligns with the anchor.
`grab` fires on press, `dragTo` per move with the finger's window x,
`release` when the drag ends. -/
composable def selectionHandle (h : SelectionHandle) (anchor : Rect)
    (color : Color) (grab : IO Unit) (dragTo : Float32 → IO Unit)
    (release : IO Unit) : Composable Unit := do
  let density ← LocalDensity.current
  let cb ← rememberUpdatedRef (grab, dragTo, release)
  let box ← remember (IO.mkRef Rect.zero)
  let id ← remember freshId
  -- Align the tip corner with the anchor point: the end handle's tip is the
  -- box's top-left (no offset), the start handle's its top-right.
  let offX : Int32 := match h with
    | .start => -(density.dpRoundToPx chromeHandleTouch)
    | .«end» => 0
  Popup (anchor := some anchor) (offset := ⟨offX, 0⟩) do
    let m := Modifier.size chromeHandleTouch chromeHandleTouch
      |>.focusNeutral
      |>.onGloballyPositioned box.set
      |>.pointerInput (mixKeys (stringKey "Compose.SelectionHandle") id.toUInt64)
          (handleDragLoop cb box)
      |>.drawBehind (drawHandleGlyph h color)
    Layout m .leaf (policyInputs := some 0x73656c68)

/-- One fixed-width toolbar text button (fixed so tap targets are
computable in tests). Deliberately NOT `Modifier.clickable`: that bundles
`focusable`, and a chrome button must never become the focus target — the
tap has to leave the field's focus (and so its IME session) untouched. -/
composable def toolbarButton (label : String) (action : IO Unit) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let actionRef ← rememberUpdatedRef action
  let id ← remember freshId
  Box (modifier := Modifier.size chromeToolbarButtonWidth chromeToolbarHeight
        |>.focusNeutral
        |>.pointerInput
            (mixKeys (stringKey "Compose.TextFieldToolbar.button") id.toUInt64)
            (detectTapGestures (onTap := some fun _ => do (← actionRef.get))))
      (contentAlignment := .center) do
    Text label (color := some colors.primary)

/-- The floating Cut/Copy/Paste toolbar over a touch selection: a
focus-neutral, non-dismissable popup preferring the space *above* the
selection rect (`Popup (preferAbove := true)`), falling back below it near
the window top. Paste appears only when the clipboard has text. Dismissal
is the field's reducer's job — every action edits or collapses, and the
chrome hides through that. -/
composable def TextFieldToolbar (anchor : Rect) (canPaste : Bool)
    (onCut onCopy onPaste : IO Unit) (modifier : Modifier := {}) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shapes ← MaterialTheme.shapes
  let tokens ← MaterialTheme.tokens
  let density ← LocalDensity.current
  Popup (anchor := some anchor) (preferAbove := true)
      (offset := ⟨0, density.dpRoundToPx chromeToolbarGap⟩) do
    Surface (modifier := modifier.focusNeutral) (shape := shapes.small)
        (color := some colors.surfaceContainer)
        (border := some { width := 1, color := colors.outline })
        (elevation := tokens.elevations.menu)
        (material := some tokens.materials.chrome) do
      Row do
        toolbarButton "Cut" onCut
        toolbarButton "Copy" onCopy
        if canPaste then toolbarButton "Paste" onPaste

end Compose

end
