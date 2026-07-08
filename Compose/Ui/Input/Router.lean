import Compose.Ui.Input.Focus
import Compose.Ui.Input.Hover
import Compose.Ui.Window

namespace Compose

/-!
# Input router (`Compose/Ui/Input/Router.lean`)

Ties the M6 pieces together per window: `InputManager` owns the pointer
capture path, the hover state, the button/position bookkeeping, and the
`FocusManager`, and routes already-translated `PointerEvent`/`KeyEvent`s
(tests drive this layer directly with a fake scheduler); `installInput`
translates SDL events (window→render coordinates via
`Renderer.coordinatesFromWindow`) and plugs the manager into
`WindowContext.inputSink` — `Compose.bootstrap` calls it, mirroring the event
bridge of `androidx.compose.ui.platform.ComposeSceneMediator`.

**Capture**: a press captures its hit path; while any button is held, moves
and releases go to the captured path (positions still localized live), so
drags keep receiving events outside the pressed node and a release outside
its bounds reaches the press handler (which sees it out of bounds — click
cancel). Hover diffing is frozen while captured and re-run on the final
release. A window-leave `exit` cancels the capture (delivered to the captured
path first, so drags can cancel).

**Key fallbacks** (app level, after `Modifier.onKeyEvent` routing): Tab /
Shift-Tab traverse the focusables, Esc clears focus.
-/

/-- Per-window input state; create via `InputManager.create` (headless tests)
or `installInput` (real windows). -/
structure InputManager where
  /-- The hit-tested tree (the window's root layout node). -/
  root : LayoutNode
  focus : FocusManager
  hover : HoverState
  /-- Hit path captured by the last press; non-empty while a button is held. -/
  capture : IO.Ref (Array HitTarget)
  /-- Buttons currently held (tracked from press/release events so synthetic
  tests need no SDL mouse state). -/
  buttonsHeld : IO.Ref Sdl.MouseButtonFlags
  /-- Last pointer position in render px (window-leave synthesizes its `exit`
  here; scroll fallback position). -/
  lastPos : IO.Ref Offset

namespace InputManager

/-- Fresh manager over `root`. `onFocusTarget` runs after every focus change
(see `FocusManager`); `installInput` uses it for the M11 text-input hook. -/
def create (root : LayoutNode) (cursor : CursorSetter)
    (onFocusTarget : Option LayoutNode → IO Unit := fun _ => pure ()) : IO InputManager :=
  return { root
           focus := ← FocusManager.create root onFocusTarget
           hover := ← HoverState.create cursor
           capture := ← IO.mkRef #[]
           buttonsHeld := ← IO.mkRef .none
           lastPos := ← IO.mkRef .zero }

/-- Mask of a possibly-absent button. -/
private def maskOf : Option Sdl.MouseButton → Sdl.MouseButtonFlags
  | some b => .mask b
  | none => .none

/-- Route one already-translated pointer event (position in render-px root
coordinates; `buttons` is filled in from the tracked state). Returns whether
some handler consumed it. The dispatch entry point tests drive directly. -/
def pointerEvent (im : InputManager) (ev : PointerEvent) : IO Bool := do
  match ev.eventType with
  | .press =>
    im.lastPos.set ev.position
    let heldBefore ← im.buttonsHeld.get
    let held ← im.buttonsHeld.modifyGet fun h =>
      let h' := h ||| maskOf ev.button
      (h', h')
    if heldBefore == .none then
      let path ← im.root.hitTest ev.position
      im.capture.set path
      -- Click-to-focus before delivery: handlers observe the updated focus.
      im.focus.focusOnPress path
      dispatchToPath path { ev with buttons := held }
    else
      -- A second button mid-gesture stays with the captured path.
      dispatchToPath (← im.capture.get) { ev with buttons := held }
  | .release =>
    im.lastPos.set ev.position
    let held ← im.buttonsHeld.modifyGet fun h =>
      let h' := h &&& ~~~(maskOf ev.button)
      (h', h')
    let path ← im.capture.get
    let path ← if path.isEmpty then im.root.hitTest ev.position else pure path
    let consumed ← dispatchToPath path { ev with buttons := held }
    if held == .none then
      im.capture.set #[]
      -- Hover was frozen during the capture; rediff at the release position.
      let _ ← im.hover.update im.root ev (some ev.position)
    return consumed
  | .move =>
    im.lastPos.set ev.position
    let ev := { ev with buttons := ← im.buttonsHeld.get }
    let captured ← im.capture.get
    if captured.isEmpty then
      let path ← im.hover.update im.root ev (some ev.position)
      dispatchToPath path ev
    else
      dispatchToPath captured ev
  | .scroll =>
    dispatchToPath (← im.root.hitTest ev.position) ev
  | .exit =>
    -- Pointer left the window: cancel any capture (delivered as `exit` so
    -- gestures like drag can cancel), then clear the hover path.
    let captured ← im.capture.get
    unless captured.isEmpty do
      let _ ← dispatchToPath captured ev
      im.capture.set #[]
      im.buttonsHeld.set .none
    let _ ← im.hover.update im.root ev none
    return true
  | .enter =>
    return false

/-- Route one key event: `Modifier.onKeyEvent` chain first (focused node,
then ancestors), then the app fallbacks — Tab/Shift-Tab traversal, Esc
clears focus. Returns whether anything handled it. -/
def keyEvent (im : InputManager) (ke : KeyEvent) : IO Bool := do
  if ← im.focus.dispatchKey ke then return true
  if ke.down && ke.key == .tab then
    im.focus.moveFocus (backward := ke.hasShift)
    return true
  if ke.down && ke.key == .escape then
    if (← im.focus.focused).isSome then
      im.focus.clearFocus
      return true
  return false

/-- Route committed text to the focused node (`Modifier.onTextInput`). -/
def textInput (im : InputManager) (text : String) : IO Bool :=
  im.focus.dispatchTextInput text

/-- Route an IME composition (`textEditing`) update to the focused node
(`Modifier.onTextEditing`). M11 addition. -/
def textEditing (im : InputManager) (text : String) (start length : Int32) : IO Bool :=
  im.focus.dispatchTextEditing text start length

end InputManager

/-- Translate one SDL event and route it through the manager (`conv` maps
window coordinates to render px). `true` = the event was input and handled. -/
def InputManager.sdlEvent (im : InputManager)
    (conv : Float32 → Float32 → IO Offset) (e : Sdl.Event) : IO Bool := do
  match e with
  | .mouseMotion me =>
    im.pointerEvent
      { eventType := .move, position := ← conv me.x me.y
        mods := ← Sdl.getModState, timestamp := me.timestamp }
  | .mouseButtonDown be =>
    im.pointerEvent
      { eventType := .press, position := ← conv be.x be.y, button := some be.button
        clicks := be.clicks, mods := ← Sdl.getModState, timestamp := be.timestamp }
  | .mouseButtonUp be =>
    im.pointerEvent
      { eventType := .release, position := ← conv be.x be.y, button := some be.button
        clicks := be.clicks, mods := ← Sdl.getModState, timestamp := be.timestamp }
  | .mouseWheel we =>
    -- Wheel deltas are in scroll ticks; `flipped` ("natural") direction is
    -- normalized so consumers always see one convention.
    let flip : Float32 := if we.direction == .flipped then -1 else 1
    im.pointerEvent
      { eventType := .scroll, position := ← conv we.mouseX we.mouseY
        scrollDelta := ⟨we.x * flip, we.y * flip⟩
        mods := ← Sdl.getModState, timestamp := we.timestamp }
  | .keyDown ke | .keyUp ke =>
    im.keyEvent (.ofSdl ke)
  | .textInput te =>
    im.textInput te.text
  | .textEditing te =>
    im.textEditing te.text te.start te.length
  | .windowMouseLeave _ =>
    im.pointerEvent { eventType := .exit, position := ← im.lastPos.get }
  | _ => return false

/-- Build the window's input pipeline and set it as the
`WindowContext.inputSink`: SDL events are translated (window→render
coordinates through the renderer) and routed into the layout tree.
`Compose.bootstrap` calls this with the defaults; tests re-install with a
recording `CursorSetter` to observe cursor changes.

`onTextClientFocused` is the documented M11 IME hook: called with `true` when
focus lands on a text-input client (a node with `Modifier.onTextInput`) and
`false` when it leaves one — M11 wires `Window.startTextInput`/`stopTextInput`
here. -/
def installInput (ctx : WindowContext) (cursor : Option CursorSetter := none)
    (onTextClientFocused : Bool → IO Unit := fun _ => pure ()) : IO InputManager := do
  let cursor ← match cursor with
    | some c => pure c
    | none => CursorSetter.sdl
  let isClient ← IO.mkRef false
  let im ← InputManager.create ctx.root cursor (onFocusTarget := fun target => do
    let now ← match target with
      | some n => do pure (← n.data).modifier.isTextInputClient
      | none => pure false
    unless (← isClient.get) == now do
      isClient.set now
      onTextClientFocused now)
  let conv := fun x y => do
    let (rx, ry) ← ctx.renderer.coordinatesFromWindow x y
    pure (⟨rx, ry⟩ : Offset)
  ctx.inputSink.set (im.sdlEvent conv)
  return im

end Compose
