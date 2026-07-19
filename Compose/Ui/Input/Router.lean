module

public import Compose.Ui.Input.Focus
public meta import Compose.Ui.Input.Focus
public import Compose.Ui.Input.Hover
public meta import Compose.Ui.Input.Hover
public import Compose.Ui.Input.Record
public meta import Compose.Ui.Input.Record
public import Compose.Ui.Window
public meta import Compose.Ui.Window
public import Std.Data.HashMap.Basic
public meta import Std.Data.HashMap.Basic

public section

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

**Capture**: a press captures its hit path; while any button of that pointer
is held, its moves and releases go to the captured path (positions still
localized live), so drags keep receiving events outside the pressed node and
a release outside its bounds reaches the press handler (which sees it out of
bounds — click cancel). Capture and button state are keyed by
`PointerEvent.pointerId` — the mouse is pointer `0`, each touch finger its
own pointer — so two fingers pressing two widgets run independent gestures.
Hover is a mouse-only concept: diffing is frozen while the mouse is captured
and re-run on its final release; finger streams never touch it. A
window-leave `exit` cancels the mouse capture; a finger's cancel (`exit`
with its id) cancels just that finger (delivered to the captured path first,
so drags can cancel).

**Tree changes**: the manager owns the root's detach hook (focus and hover
state referencing removed nodes is released — see `nodeDetached`) and chains
its remeasure-request hook to schedule a post-layout hover sync, so content
appearing or vanishing under a stationary cursor gets its enter/exit and the
cursor icon stays right (Compose synthesizes a pointer move after layout).

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
  /-- Hit path captured by each pointer's press, keyed by
  `PointerEvent.pointerId`; an entry lives while that pointer holds a
  button. -/
  captures : IO.Ref (Std.HashMap UInt64 (Array HitTarget))
  /-- Touch click-to-focus is tap-gated: a finger press *arms* the deepest
  focusable under it here (`none` = the press hit no focusable, so the tap
  clears focus); the release commits it, a steal or gesture cancel drops it
  — a drag-scroll over a text field must not pop the keyboard. Mouse
  presses focus immediately (`focusOnPress`) and never appear here. -/
  pendingFocus : IO.Ref (Std.HashMap UInt64 (Option LayoutNode))
  /-- Buttons currently held per pointer (tracked from press/release events
  so synthetic tests need no SDL mouse state). -/
  buttonsHeld : IO.Ref (Std.HashMap UInt64 Sdl.MouseButtonFlags)
  /-- Last *mouse* position in render px (window-leave synthesizes its `exit`
  here; scroll fallback position). -/
  lastPos : IO.Ref Offset
  /-- A cursor position is known and inside the window (set by
  move/press/release, cleared by window-leave `exit`); gates the post-layout
  hover sync. -/
  pointerInside : IO.Ref Bool
  /-- A post-layout hover sync is already scheduled (dedupe). -/
  hoverSyncPending : IO.Ref Bool
  /-- Scheduler the post-layout hover sync runs on (`none` disables the sync
  — minimal router tests). -/
  sched : Option Scheduler
  /-- M10 overlay key handlers (shared with `WindowContext.keyHandlers` by
  `installInput`): capture handlers run before focused-node routing, the
  rest after it, innermost (last registered) first. -/
  overlayKeys : IO.Ref (Array OverlayKeyHandler)
  /-- Observer of every event entering `pointerEvent`, before dispatch — the
  `COMPOSE_INPUT_RECORD` capture tap (see `InputRecorder`); `none` when not
  recording. -/
  tap : Option (PointerEvent → IO Unit) := none

namespace InputManager

/-- Applier detach hook: `subtree` is leaving the tree (fired before its
parent links are severed). Focus inside it is cleared through the normal
path, so the IME/text-client lifecycle fires; hovered nodes inside it get
their `exit` now — after `severParentLinks` their handlers are gone, which
would leave hover interactions latched. -/
def nodeDetached (im : InputManager) (subtree : LayoutNode) : IO Unit := do
  im.focus.clearIfDetaching subtree
  im.hover.exitDetaching subtree { eventType := .exit, position := ← im.lastPos.get }

/-- Re-run the hover-path diff at the last known cursor position, as if the
mouse had moved in place: enters/exits/cursor fire for content that appeared
or vanished under a stationary cursor (Compose's synthesized move after
layout changes). Skipped while a press capture holds hover frozen (the final
release rediffs) or when no in-window position is known. -/
def syncHover (im : InputManager) : IO Unit := do
  unless ← im.pointerInside.get do return
  if (← im.captures.get).contains 0 then return
  let pos ← im.lastPos.get
  let _ ← im.hover.update im.root { eventType := .move, position := pos } (some pos)

/-- The scheduled sync: wait (cooperatively) until the pending layout pass
has run — the app loop measures dirty trees before its next `runDue` — then
diff once. -/
private partial def hoverSyncTask (im : InputManager) : UiTask Unit := do
  let d ← im.root.data
  if d.needsRemeasure || d.needsRelayout then
    UiTask.yield
    im.hoverSyncTask
  else
    im.hoverSyncPending.set false
    im.syncHover

/-- Schedule one `syncHover` for after the pending layout pass (deduped —
a dirty frame costs at most one extra hit test). -/
def scheduleHoverSync (im : InputManager) : IO Unit := do
  let some s := im.sched | return
  unless ← im.pointerInside.get do return
  if ← im.hoverSyncPending.modifyGet fun p => (p, true) then return
  let _ ← s.launch im.hoverSyncTask

/-- Fresh manager over `root`. `onFocusTarget` runs after every focus change
(see `FocusManager`); `installInput` uses it for the M11 text-input hook.
`overlayKeys` shares the window's overlay key-handler registry (a fresh empty
one when absent — headless router tests). Installs itself as `root`'s detach
hook (single consumer — re-installing input rebinds it) and, given `sched`,
chains the root's remeasure-request hook to schedule the post-layout hover
sync. -/
def create (root : LayoutNode) (cursor : CursorSetter)
    (onFocusTarget : Option LayoutNode → IO Unit := fun _ => pure ())
    (overlayKeys : Option (IO.Ref (Array OverlayKeyHandler)) := none)
    (sched : Option Scheduler := none)
    (tap : Option (PointerEvent → IO Unit) := none) : IO InputManager := do
  let im : InputManager :=
    { root, sched, tap
      focus := ← FocusManager.create root onFocusTarget
      hover := ← HoverState.create cursor
      captures := ← IO.mkRef {}
      pendingFocus := ← IO.mkRef {}
      buttonsHeld := ← IO.mkRef {}
      lastPos := ← IO.mkRef .zero
      pointerInside := ← IO.mkRef false
      hoverSyncPending := ← IO.mkRef false
      overlayKeys := ← match overlayKeys with
        | some r => pure r
        | none => IO.mkRef #[] }
  root.setOnDetach im.nodeDetached
  if sched.isSome then
    let prev := (← root.data).onRequestRemeasure
    root.setOnRequestRemeasure do
      if let some notify := prev then notify
      im.scheduleHoverSync
  return im

/-- Hand pointer `pid`'s in-flight gesture to its captured-path node `nid`
(a `PointerEvent.steal` request from one of its handlers): targets *inner*
to it are cut from that pointer's capture and receive a synthetic `exit` —
the same gesture-cancel a window leave delivers — so a pending press (a
clickable under the finger when a drag-scroll takes over) cancels instead of
clicking. Outer targets stay captured (`PointerPass.final` observers there
keep watching the gesture). -/
def stealCapture (im : InputManager) (pid : UInt64) (nid : Nat) (pos : Offset) : IO Unit := do
  let path := (← im.captures.get).getD pid #[]
  let mut cut : Option Nat := none
  for i in [0:path.size] do
    if cut.isNone then
      if (← path[i]!.node.nodeId) == nid then cut := some i
  let some i := cut | return
  -- The takeover cancels the tap: an armed touch focus must not commit on
  -- the up (the finger is scrolling, not tapping the focusable).
  im.pendingFocus.modify (·.erase pid)
  let inner := path.extract (i + 1) path.size
  unless inner.isEmpty do
    im.captures.modify (·.insert pid (path.extract 0 (i + 1)))
    let _ ← dispatchToPath inner { eventType := .exit, position := pos, pointerId := pid }

/-- Mask of a possibly-absent button. -/
private def maskOf : Option Sdl.MouseButton → Sdl.MouseButtonFlags
  | some b => .mask b
  | none => .none

/-- Route one already-translated pointer event (position in render-px root
coordinates; `buttons` is filled in from the tracked state, both keyed by
`ev.pointerId`). Returns whether some handler consumed it. The dispatch
entry point tests drive directly. Hover and the last-known cursor position
are mouse concepts (pointer `0` only). -/
def pointerEvent (im : InputManager) (ev : PointerEvent) : IO Bool := do
  if let some t := im.tap then t ev
  let pid := ev.pointerId
  let isMouse := pid == 0
  match ev.eventType with
  | .press =>
    if isMouse then
      im.lastPos.set ev.position
      im.pointerInside.set true
    let heldBefore := (← im.buttonsHeld.get).getD pid .none
    let held := heldBefore ||| maskOf ev.button
    im.buttonsHeld.modify (·.insert pid held)
    if heldBefore == .none then
      let path ← im.root.hitTest ev.position
      im.captures.modify (·.insert pid path)
      -- Click-to-focus before delivery: handlers observe the updated focus.
      -- Mouse only — a finger arms a tap-gated pending focus instead,
      -- committed at the release (Android focuses on the tap, not the
      -- touch-down: a drag-scroll starting on a text field never focuses).
      if isMouse then
        im.focus.focusOnPress path
      else
        -- Focus-neutral chrome (selection handles/toolbar) arms nothing:
        -- the current focus must survive the tap.
        match ← FocusManager.focusPress path with
        | .focus n => im.pendingFocus.modify (·.insert pid (some n))
        | .clear => im.pendingFocus.modify (·.insert pid none)
        | .keep => pure ()
      dispatchToPath path { ev with buttons := held }
    else
      -- A second button mid-gesture stays with the captured path.
      dispatchToPath ((← im.captures.get).getD pid #[]) { ev with buttons := held }
  | .release =>
    if isMouse then
      im.lastPos.set ev.position
      im.pointerInside.set true
    let held := ((← im.buttonsHeld.get).getD pid .none) &&& ~~~(maskOf ev.button)
    im.buttonsHeld.modify fun h =>
      if held == .none then h.erase pid else h.insert pid held
    let path := (← im.captures.get).getD pid #[]
    let path ← if path.isEmpty then im.root.hitTest ev.position else pure path
    -- A finger tap commits its armed focus at the up — before delivery, so
    -- release handlers observe the updated focus (the ordering mouse gets
    -- at press time). A steal or cancel already dropped the entry.
    if !isMouse && held == .none then
      if let some cand := (← im.pendingFocus.get).get? pid then
        im.pendingFocus.modify (·.erase pid)
        match cand with
        | some n =>
          if ← im.focus.isAttached n then im.focus.requestFocus (some n)
          else im.focus.clearFocus
        | none => im.focus.clearFocus
    let consumed ← dispatchToPath path { ev with buttons := held }
    if held == .none then
      im.captures.modify (·.erase pid)
      -- Mouse hover was frozen during the capture; rediff at the release
      -- position. Fingers have no hover to restore.
      if isMouse then
        let _ ← im.hover.update im.root ev (some ev.position)
    return consumed
  | .move =>
    if isMouse then
      im.lastPos.set ev.position
      im.pointerInside.set true
    let ev := { ev with buttons := (← im.buttonsHeld.get).getD pid .none }
    let captured := (← im.captures.get).getD pid #[]
    if captured.isEmpty then
      if isMouse then
        let path ← im.hover.update im.root ev (some ev.position)
        dispatchToPath path ev
      else
        -- A finger only exists while touching: an uncaptured finger move
        -- (its press path vanished mid-gesture) has nowhere to go.
        return false
    else
      -- Captured moves may carry a takeover request (`PointerEvent.steal`):
      -- a drag-scroll passing its touch slop claims the gesture from the
      -- pressed child.
      let stealSlot ← IO.mkRef (none : Option Nat)
      let consumed ← dispatchToPath captured ev (stealSlot := some stealSlot)
      if let some nid ← stealSlot.get then
        im.stealCapture pid nid ev.position
      return consumed
  | .scroll =>
    dispatchToPath (← im.root.hitTest ev.position) ev
  | .pinch =>
    dispatchToPath (← im.root.hitTest ev.position) ev
  | .exit =>
    -- Pointer gone: the mouse left the window, or a finger's gesture was
    -- cancelled (the system stole it — e.g. Android's back-gesture monitor).
    -- Cancel that pointer's capture (delivered as `exit` so gestures like
    -- drag can cancel); only a mouse leave also clears the hover path.
    if isMouse then
      im.pointerInside.set false
    let captured := (← im.captures.get).getD pid #[]
    im.pendingFocus.modify (·.erase pid)
    unless captured.isEmpty do
      let _ ← dispatchToPath captured ev
      im.captures.modify (·.erase pid)
      im.buttonsHeld.modify (·.erase pid)
    if isMouse then
      let _ ← im.hover.update im.root ev none
    return true
  | .enter =>
    return false

/-- Run the registered overlay key handlers of the given phase, innermost
(last registered) first; `true` = consumed. The registry is re-read from the
shared ref so a handler that unregisters others (a dismiss) is safe. -/
private def runOverlayKeys (im : InputManager) (capture : Bool) (ke : KeyEvent) : IO Bool := do
  let hs ← im.overlayKeys.get
  for i in [0:hs.size] do
    let h := hs[hs.size - 1 - i]!
    if h.capture == capture then
      if ← h.handler ke then return true
  return false

/-- Route one key event: overlay *capture* handlers first (a focusable popup
grabs the keyboard while open), then the `Modifier.onKeyEvent` chain (focused
node, then ancestors), then the remaining overlay handlers (Esc-dismiss,
innermost first), then the app fallbacks — Tab/Shift-Tab traversal, Esc
clears focus. Returns whether anything handled it. -/
def keyEvent (im : InputManager) (ke : KeyEvent) : IO Bool := do
  if ← im.runOverlayKeys (capture := true) ke then return true
  if ← im.focus.dispatchKey ke then return true
  if ← im.runOverlayKeys (capture := false) ke then return true
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
window coordinates to render px; `winSize` is the window size in the same
coordinates finger events are normalized against — touch positions are
`0..1` fractions of it). `true` = the event was input and handled.

Touch fingers arrive as their own pointer streams (`fingerId + 1`; the mouse
is pointer `0`) — `initVideo` turns SDL's touch→mouse synthesis off, so a
tap is delivered exactly once. A finger has no button; its contact is
modeled as a left press so the existing gesture detectors run unchanged. -/
def InputManager.sdlEvent (im : InputManager)
    (conv : Float32 → Float32 → IO Offset) (e : Sdl.Event)
    (winSize : IO (Float32 × Float32) := pure (1, 1)) : IO Bool := do
  let fingerPos (fe : Sdl.TouchFingerEvent) : IO Offset := do
    let (w, h) ← winSize
    conv (fe.x * w) (fe.y * h)
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
    -- Wheel deltas are in scroll ticks, used exactly as delivered: the OS has
    -- already applied the user's scroll-direction preference (macOS "natural
    -- scrolling"), so the values are in *content* terms. `.flipped` only marks
    -- that they differ from raw device motion (for apps that want the raw
    -- direction, e.g. wheel-as-zoom) — negating it here would undo the user's
    -- system preference and reverse trackpad scrolling.
    im.pointerEvent
      { eventType := .scroll, position := ← conv we.mouseX we.mouseY
        scrollDelta := ⟨we.x, we.y⟩
        mods := ← Sdl.getModState, timestamp := we.timestamp }
  | .keyDown ke | .keyUp ke =>
    im.keyEvent (.ofSdl ke)
  | .textInput te =>
    im.textInput te.text
  | .textEditing te =>
    im.textEditing te.text te.start te.length
  | .fingerDown fe =>
    im.pointerEvent
      { eventType := .press, position := ← fingerPos fe
        pointerId := fe.fingerId.val + 1, button := some .left, clicks := 1
        mods := ← Sdl.getModState, timestamp := fe.timestamp }
  | .fingerMotion fe =>
    im.pointerEvent
      { eventType := .move, position := ← fingerPos fe
        pointerId := fe.fingerId.val + 1
        mods := ← Sdl.getModState, timestamp := fe.timestamp }
  | .fingerUp fe =>
    im.pointerEvent
      { eventType := .release, position := ← fingerPos fe
        pointerId := fe.fingerId.val + 1, button := some .left, clicks := 1
        mods := ← Sdl.getModState, timestamp := fe.timestamp }
  | .fingerCanceled fe =>
    -- The system stole the gesture (Android's back-gesture / notification
    -- monitors): cancel, don't click.
    im.pointerEvent
      { eventType := .exit, position := ← fingerPos fe
        pointerId := fe.fingerId.val + 1, timestamp := fe.timestamp }
  | .windowMouseLeave _ =>
    im.pointerEvent { eventType := .exit, position := ← im.lastPos.get }
  | .pinchUpdate pe =>
    -- Android delivers finger streams *and* pinch events for one gesture
    -- (SDLSurface feeds both) — fingers own it whenever any is captured, so
    -- the routed event is effectively the desktop-trackpad path (where no
    -- finger events exist and the cursor marks the target).
    if (← im.captures.get).keys.any (· != 0) then return true
    im.pointerEvent
      { eventType := .pinch, position := ← im.lastPos.get
        zoomDelta := pe.scale, timestamp := pe.timestamp }
  | .pinchBegin _ | .pinchEnd _ =>
    -- Only the scale steps carry information; the bracketing is implicit.
    return true
  | _ => return false

/-- Build the window's input pipeline and set it as the
`WindowContext.inputSink`: SDL events are translated (window→render
coordinates through the renderer) and routed into the layout tree.
`Compose.bootstrap` calls this with the defaults; tests re-install with a
recording `CursorSetter` to observe cursor changes.

`onTextClientFocused` is the documented M11 IME hook: called with `true` when
focus lands on a text-input client (a node with `Modifier.onTextInput`) and
`false` when it leaves one — M11 wires `Window.startTextInput`/`stopTextInput`
here.

`COMPOSE_INPUT_RECORD=<path>` installs an `InputRecorder` as the manager's
`tap` (and as the window's `frameProbe`), dumping the translated event
stream for headless replay — see `Compose.Ui.Input.Record`. -/
def installInput (ctx : WindowContext) (cursor : Option CursorSetter := none)
    (onTextClientFocused : Bool → IO Unit := fun _ => pure ()) : IO InputManager := do
  let cursor ← match cursor with
    | some c => pure c
    | none => CursorSetter.sdl
  -- Empty counts as unset: Android's SDL_ENV.* manifest injection sets the
  -- variable even when the placeholder is blank (the recording-off build).
  let recorder ← match ← IO.getEnv "COMPOSE_INPUT_RECORD" with
    | some path =>
      if path.isEmpty then pure none else do
        let (pw, ph) ← ctx.window.getSizeInPixels
        let density := (← ctx.densityState.get).density
        some <$> InputRecorder.create path pw ph density
    | none => pure none
  ctx.frameProbe.set (recorder.map (·.frame))
  let isClient ← IO.mkRef false
  let im ← InputManager.create ctx.root cursor
    (tap := recorder.map (·.event))
    (overlayKeys := some ctx.keyHandlers)
    (sched := some ctx.scheduler)
    (onFocusTarget := fun target => do
    -- Focus gain (click, Tab, FocusRequester, modal restore) reveals the
    -- new target — Compose's focusable requests bringIntoView on gain.
    if target.isSome then ctx.requestBringIntoView
    let now ← match target with
      | some n => do pure (← n.data).modifier.isTextInputClient
      | none => pure false
    unless (← isClient.get) == now do
      isClient.set now
      onTextClientFocused now)
  let conv := fun x y => do
    let (rx, ry) ← ctx.backend.coordinatesFromWindow x y
    pure (⟨rx, ry⟩ : Offset)
  let winSize := do
    let (ww, wh) ← ctx.window.getSize
    pure (ww.toFloat32, wh.toFloat32)
  -- Modal overlays (Dialog) scope Tab traversal to their subtree and restore
  -- prior focus on close, through the focus manager.
  ctx.modalFocusHook.set fun id opening =>
    if opening then im.focus.pushModalScope id else im.focus.popModalScope id
  ctx.inputSink.set (im.sdlEvent conv (winSize := winSize))
  -- M14b: publish the focus manager so composition-side FocusRequesters
  -- (rememberFocusRequester) can reach it.
  ctx.focusManager.set (some im.focus)
  return im

/-- Create a `FocusRequester` remembered at this composition position, bound
to the ambient window's focus manager: attach it with
`Modifier.focusRequester` (plus `Modifier.focusable`) and call
`.requestFocus` from handlers or effects. Mirrors
`remember { FocusRequester() }` + `androidx.compose.ui.focus.FocusRequester`. -/
def rememberFocusRequester : Composable FocusRequester := do
  let ctx? ← LocalWindowContext.current
  remember do
    let manager ← match ctx? with
      | some ctx => pure ctx.focusManager
      | none => IO.mkRef none
    return { id := (← freshId).toUInt64, manager }

end Compose

end
