import Compose.Ui.Window
import Compose.Ui.Layout
import Compose.Runtime.Macro

namespace Compose

/-!
# Overlays: host, `Popup`, `Dialog` (`Compose/Ui/Overlay.lean`)

The in-window overlay system from DESIGN.md. `WindowContext.overlays` is a
state list of `OverlayEntry`s; the **overlay host** (composed by `bootstrap`
right after the main content) turns each entry into an independent
full-window layout subtree under the window root — measured with window
constraints, drawn after the main content in registration order, and
hit-tested first (reverse draw order), so overlays sit on top with no
changes to the input pipeline.

* `Popup` registers/unregisters its entry on enter/leave (`remember` +
  `DisposableEffect`). Content is positioned relative to an anchor rect
  (captured at the call site via `Modifier.onGloballyPositioned`) or by
  window alignment, clamped to the window and flipped above the anchor when
  there is no room below. When dismissable, a click landing outside the
  content (a full-window transparent input layer *under* the content within
  the same entry) and Esc (an app-level key-handler registration, innermost
  overlay first) call `onDismissRequest`. Mirrors
  `androidx.compose.ui.window.Popup`.
* `Dialog` is the modal variant: a full-window scrim (black at 32 %) that
  swallows every pointer event below it, content centered, Esc/scrim-click
  dismiss. Mirrors `androidx.compose.ui.window.Dialog` (in-window).

Overlay content composes under the `CompositionLocal` scope captured at the
owner's call site, so it sees the theme/density/scheduler of where the
`Popup` sits — the analog of a Compose popup inheriting the parent
`CompositionContext`. The owner refreshes the entry (and bumps its revision)
every composition, so the popup recomposes with its caller.
-/

/-- The dialog scrim: black at the Material 32 % scrim opacity (both
baseline schemes use a black scrim; `Dialog` lives below the theme layer, so
the color is fixed here). -/
def dialogScrimColor : Color := Color.black.withAlpha 0.32

/-! ## Position resolution -/

/-- Resolve a popup's content position inside the window: below the anchor
(offset applied), flipped above it when there is no room below but room
above, else window-`alignment` + offset — always clamped into the window.
Mirrors `PopupPositionProvider.calculatePosition` (dropdown flavor). -/
def resolvePopupPosition (window contentSize : IntSize) (anchor : Option Rect)
    (alignment : Alignment) (offset : IntOffset) : IntOffset :=
  let (x, y) :=
    match anchor with
    | some a =>
      let below := roundHalfUp a.bottom + offset.y
      let y :=
        if below + contentSize.height > window.height then
          let above := roundHalfUp a.top - contentSize.height - offset.y
          if above ≥ 0 then above else below
        else below
      (roundHalfUp a.left + offset.x, y)
    | none =>
      let p := alignment.align contentSize window
      (p.x + offset.x, p.y + offset.y)
  ⟨min (max x 0) (max 0 (window.width - contentSize.width)),
   min (max y 0) (max 0 (window.height - contentSize.height))⟩

-- Below a mid-window anchor, offset applied.
#guard resolvePopupPosition ⟨200, 200⟩ ⟨50, 40⟩ (some ⟨10, 20, 60, 40⟩) .topStart ⟨0, 4⟩
        == ⟨10, 44⟩
-- No room below (anchor near the bottom): flips above.
#guard resolvePopupPosition ⟨200, 200⟩ ⟨50, 40⟩ (some ⟨10, 170, 60, 190⟩) .topStart ⟨0, 0⟩
        == ⟨10, 130⟩
-- No room either side: stays below, clamped into the window.
#guard resolvePopupPosition ⟨200, 60⟩ ⟨50, 40⟩ (some ⟨10, 10, 60, 50⟩) .topStart ⟨0, 0⟩
        == ⟨10, 20⟩
-- Horizontal clamp at the right edge.
#guard resolvePopupPosition ⟨100, 200⟩ ⟨50, 40⟩ (some ⟨80, 20, 90, 40⟩) .topStart ⟨0, 0⟩
        == ⟨50, 40⟩
-- No anchor: aligned in the window.
#guard resolvePopupPosition ⟨200, 100⟩ ⟨50, 40⟩ none .center ⟨0, 0⟩ == ⟨75, 30⟩
#guard resolvePopupPosition ⟨200, 100⟩ ⟨50, 40⟩ none .bottomEnd ⟨0, 0⟩ == ⟨150, 60⟩
-- Oversized content clamps to the origin instead of going negative.
#guard resolvePopupPosition ⟨100, 100⟩ ⟨120, 40⟩ none .center ⟨0, 0⟩ == ⟨0, 30⟩

/-- Identity of the position inputs, for the layer policy's `policyInputs`. -/
private def positionKey (anchor : Option Rect) (a : Alignment) (o : IntOffset) : UInt64 :=
  let anchorK := match anchor with
    | none => 1
    | some r => mixKeys r.left.toBits.toUInt64 <| mixKeys r.top.toBits.toUInt64 <|
        mixKeys r.right.toBits.toUInt64 r.bottom.toBits.toUInt64
  mixKeys anchorK <| mixKeys a.horizontalBias.toBits.toUInt64 <|
    mixKeys a.verticalBias.toBits.toUInt64 <|
      mixKeys o.x.toFloat32.toBits.toUInt64 o.y.toFloat32.toBits.toUInt64

/-! ## Layer input coroutines (self-contained — `Ui` cannot use foundation's
gesture detectors) -/

/-- Consume presses (calling `dismiss`) and releases — the transparent
outside-click layer of a dismissable popup / the dialog scrim. -/
private partial def dismissClicks (dismiss : IO.Ref (Option (IO Unit)))
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .press =>
    ev.consume
    if let some f ← dismiss.get then f
  | .release => ev.consume
  | _ => pure ()
  dismissClicks dismiss scope

/-- Consume clicks nothing inner handled — makes the popup content surface
opaque to input (a click *inside* the popup must not fall through to the
outside-click layer below it). -/
private partial def swallowClicks (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .press || ev.eventType == .release then
    ev.consume
  swallowClicks scope

/-! ## The overlay layer -/

/-- Measure policy of one overlay layer: the layer fills the window; an
optional scrim child (present when the children count is 2) fills it too;
the content child measures loose within the window and is placed by
`resolvePopupPosition`. -/
private def layerPolicy (anchor : Option Rect) (alignment : Alignment)
    (offset : IntOffset) : MeasurePolicy := fun _ ms c => do
  let win : IntSize :=
    ⟨if c.hasBoundedWidth then c.maxWidth else c.minWidth,
     if c.hasBoundedHeight then c.maxHeight else c.minHeight⟩
  if ms.isEmpty then return { size := win }
  let scrim? ← if ms.size ≥ 2 then
      some <$> ms[0]!.measure (Constraints.fixed win.width win.height)
    else pure none
  let content ← ms[ms.size - 1]!.measure { maxWidth := win.width, maxHeight := win.height }
  let pos := resolvePopupPosition win ⟨content.width, content.height⟩ anchor alignment offset
  return { size := win
           placement := do
             if let some s := scrim? then s.placeAt .zero
             content.placeAt pos }

/-- One overlay entry's full-window subtree: `[scrim/outside-click layer?,
content wrapper]` under the positioning policy above. `scrimColor`/`modal`
distinguish `Dialog` (colored, swallows wheel) from `Popup` (transparent
click-catcher only when dismissable). An `interactive := false` layer is inert:
no outside-click scrim and the whole subtree is excluded from hit-testing, so a
dismissed popup fading out intercepts nothing (Compose semantics). -/
private def overlayLayerContent (id : Nat) (anchor : Option Rect)
    (alignment : Alignment) (offset : IntOffset)
    (dismiss : IO.Ref (Option (IO Unit))) (dismissable : Bool)
    (scrimColor : Option Color) (modal : Bool) (interactive : Bool)
    (content : Composable Unit) : Composable Unit :=
  Layout {} (layerPolicy anchor alignment offset)
    (policyInputs := some (mixKeys 0x6f766c79 (positionKey anchor alignment offset)))
    (hitTestable := interactive) do
    if interactive && (dismissable || modal) then
      withGroup 0x736372 do
        let m := Modifier.pointerInput
            (mixKeys (stringKey "Compose.Overlay.scrim") id.toUInt64)
            (dismissClicks dismiss)
          |>.then (match scrimColor with
                   | some col => Modifier.background col
                   | none => {})
          |>.then (if modal then Modifier.onScroll (fun d => pure d) else {})
        Layout m .leaf (policyInputs := some 0x736372)
    else
      withGroup 0x6e736372 (pure ())
    -- A modal overlay marks its content subtree a focus scope, confining Tab
    -- traversal to it while open (see `FocusManager.focusables`).
    let contentMod := Modifier.pointerInput
        (mixKeys (stringKey "Compose.Overlay.content") id.toUInt64) swallowClicks
    let contentMod := if modal then contentMod.focusScope id else contentMod
    Layout contentMod .root content (policyInputs := some 0x63747277)

/-! ## The host -/

/-- Swap in the `CompositionLocal` scope captured at the overlay owner's call
site for the duration of `body` (see the module docstring). -/
private def withCapturedLocals (saved : LocalMap) (body : Composable Unit) :
    Composable Unit := fun c => do
  let cur ← c.locals.get
  c.locals.set saved
  tryFinally (body.run c) (c.locals.set cur)

/-- One host layer: recomposes when the owning overlay refreshes its entry
(the revision read) and composes the entry's latest content under its
captured locals. -/
composable def overlayLayer (entry : OverlayEntry) : Composable Unit := do
  let _ ← entry.revision.get
  let body ← entry.content.get
  let saved ← entry.locals.get
  withCapturedLocals saved body

/-- The overlay host: one independent layer per registered entry, in
registration order (later entries draw on top and are hit first). Composed
by `bootstrap` right after the main content, as a sibling subtree under the
window root. -/
composable def overlayHost (ctx : WindowContext) : Composable Unit := do
  let entries ← ctx.overlays.get
  for entry in entries do
    keyed entry.id (overlayLayer entry)

/-- The root content wrapper `bootstrap` composes: the app content, then the
overlay host (its layers become later — topmost — children of the window
root). -/
def WindowContext.withOverlayHost (ctx : WindowContext) (content : Composable Unit) :
    Composable Unit := do
  content
  overlayHost ctx

/-! ## Popup and Dialog -/

/-- A remembered ref refreshed to `value` every composition — reads from
long-lived callbacks stay current (the `rememberUpdatedState` idiom). -/
private def updatedRef [Nonempty α] (value : α) : Composable (IO.Ref α) := do
  let r ← remember (IO.mkRef value)
  r.set value
  return r

/-- Read the composer's current `CompositionLocal` scope (captured for the
overlay entry). -/
private def captureLocals : Composable LocalMap := fun c => c.locals.get

/-- Shared implementation of `Popup` and `Dialog` (see their docstrings). -/
composable def overlayImpl (anchor : Option Rect) (alignment : Alignment)
    (offset : IntOffset) (onDismissRequest : Option (IO Unit)) (focusable : Bool)
    (onKeyEvent : KeyEvent → IO Bool) (scrimColor : Option Color) (modal : Bool)
    (interactive : Bool) (content : Composable Unit) : Composable Unit := do
  let ctx? ← LocalWindowContext.current
  match ctx? with
  | none =>
    throw (IO.userError "Compose: Popup/Dialog need a window (no LocalWindowContext)")
  | some ctx =>
    let entry : OverlayEntry ← remember do
      pure { id := ← freshId
             content := ← IO.mkRef (pure () : Composable Unit)
             revision := ← MutableState.create 0
             locals := ← IO.mkRef .empty }
    let dismissRef ← updatedRef onDismissRequest
    let keyRef ← updatedRef onKeyEvent
    -- Latest interactivity, read live by the long-lived key handler: an inert
    -- (exiting) overlay routes no keys, letting them reach normal handlers.
    let interactiveRef ← updatedRef interactive
    let locals ← captureLocals
    -- Refresh the entry every composition: latest locals + content capture,
    -- then bump the revision so the host layer recomposes with them.
    entry.locals.set locals
    entry.content.set (overlayLayerContent entry.id anchor alignment offset
      dismissRef onDismissRequest.isSome scrimColor modal interactive content)
    entry.revision.modify (· + 1)
    DisposableEffect entry.id do
      ctx.registerOverlay entry
      ctx.registerKeyHandler
        { id := entry.id
          capture := focusable
          handler := fun ke => do
            unless ← interactiveRef.get do return false
            if ← (← keyRef.get) ke then return true
            if ke.down && !ke.isRepeat && ke.key == .escape then
              match ← dismissRef.get with
              | some f => f; return true
              | none => return false
            else
              return false }
      -- Modal overlays scope focus traversal to themselves and restore the
      -- prior focus on close (see `FocusManager.pushModalScope`).
      if modal then (← ctx.modalFocusHook.get) entry.id true
      return do
        ctx.unregisterKeyHandler entry.id
        ctx.unregisterOverlay entry.id
        if modal then (← ctx.modalFocusHook.get) entry.id false

/-- Compose `content` into an overlay above the window's main content,
positioned below `anchor` (flipping above it when out of room, always
clamped to the window) or by window `alignment` when no anchor is given.
When `onDismissRequest` is set, a click landing outside the content and Esc
call it (innermost overlay first). `focusable` popups grab key routing while
open (`onKeyEvent` sees every key before the focused node). `interactive :=
false` makes the popup inert (no dismiss scrim, no key routing, transparent to
the pointer) while it is only mounted to play an exit animation. The popup
itself emits no local layout — its content lives in the window's overlay host.
Mirrors `androidx.compose.ui.window.Popup`. -/
def Popup (content : Composable Unit := pure ())
    (anchor : Option Rect := none) (alignment : Alignment := .topStart)
    (offset : IntOffset := ⟨0, 0⟩) (onDismissRequest : Option (IO Unit) := none)
    (focusable : Bool := false) (onKeyEvent : KeyEvent → IO Bool := fun _ => pure false)
    (interactive : Bool := true) : Composable Unit :=
  overlayImpl anchor alignment offset onDismissRequest focusable onKeyEvent
    (scrimColor := none) (modal := false) interactive content

/-- A modal overlay: a full-window scrim (black at 32 %) swallows every
pointer event below it, `content` is centered, and Esc or a scrim click
calls `onDismissRequest`. Mirrors `androidx.compose.ui.window.Dialog`
(in-window; keyboard focus is not scoped to the dialog — a documented M10
limitation). -/
def Dialog (onDismissRequest : IO Unit) (content : Composable Unit := pure ()) :
    Composable Unit :=
  overlayImpl (anchor := none) (alignment := .center) (offset := ⟨0, 0⟩)
    (onDismissRequest := some onDismissRequest) (focusable := true)
    (onKeyEvent := fun _ => pure false) (scrimColor := some dialogScrimColor)
    (modal := true) (interactive := true) content

end Compose
