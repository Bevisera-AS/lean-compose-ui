import Sdl
import Compose.Runtime.Recomposer
import Compose.Runtime.LaunchedEffect
import Compose.Runtime.Macro
import Compose.Ui.Node
import Compose.Ui.Input.Focus
import Compose.Ui.Text.Fonts
import Compose.Ui.Text.Paragraph
import Compose.Ui.Draw.Backend

namespace Compose

/-!
# Window context (`Compose/Ui/Window.lean`)

Per-window state for the M5 app shell: the SDL window/renderer pair, the
density derived from the display scale, the root `LayoutNode`, the
`Composition`, the coroutine `Scheduler`, and the dirty/quit flags the event
loop consumes. There is deliberately **no global window singleton** — all
per-window state lives here and reaches composables through CompositionLocals
(real multi-window later just means several contexts). Mirrors the owner-side
state of `androidx.compose.ui.platform.AndroidComposeView` + `ComposeWindow`.
-/

/-- The ambient density (display scale) for `Dp`/`Sp` resolution in
composition. Provided per window and refreshed on
`windowDisplayScaleChanged`; dynamic, so only actual readers recompose on a
scale change. Mirrors `androidx.compose.ui.platform.LocalDensity`. -/
initialize LocalDensity : CompositionLocal Density ← compositionLocalOf {}

/-- Safe-area insets: the strip along each window edge covered by system UI
(status bar, display cutout, navigation/gesture zones — populated on Android;
zero on desktop, where the whole window is safe). In `Dp`, ready for
`Modifier.padding`. Mirrors `androidx.compose.foundation.layout.WindowInsets`
(the `safeDrawing` set). -/
structure WindowInsets where
  left : Dp := 0
  top : Dp := 0
  right : Dp := 0
  bottom : Dp := 0
  deriving Repr, BEq, Inhabited

/-- Insets from SDL's safe-area rect: `safe` and the window size `(ww, wh)`
are in window coordinates; each edge distance converts to layout `Dp` by
`× pixelDensity ÷ density` (window coords → physical px → dp — see
`windowCoordSize`'s model; identity when both scales agree, as on Android
where window coords are pixels and density is the display scale ÷ that same
factor… i.e. the general form keeps every platform honest). Degenerate
metrics (`≤ 0`, e.g. dummy drivers) fall back to factor 1; negative edges
clamp to zero. -/
def WindowInsets.ofSafeArea (safe : Sdl.Rect) (ww wh : Int32)
    (pixelDensity density : Float32) : WindowInsets :=
  let edge (v : Int32) : Dp :=
    if pixelDensity > 0 && density > 0 then
      ⟨(max v 0).toFloat32 * pixelDensity / density⟩
    else
      ⟨(max v 0).toFloat32⟩
  { left := edge safe.x
    top := edge safe.y
    right := edge (ww - safe.x - safe.w)
    bottom := edge (wh - safe.y - safe.h) }

-- Full-window safe area (desktop): zero insets.
#guard WindowInsets.ofSafeArea ⟨0, 0, 400, 300⟩ 400 300 1 1 == {}
-- Android-style: window coords are pixels (pixelDensity 1), density 3 —
-- a 132 px status bar is 44 dp of top inset.
#guard WindowInsets.ofSafeArea ⟨0, 132, 1344, 2728⟩ 1344 2992 1 3
        == { top := 44, bottom := 44 }
-- Malformed rect (larger than the window) clamps to zero rather than going
-- negative; unreported metrics fall back to factor 1.
#guard WindowInsets.ofSafeArea ⟨-10, 0, 500, 300⟩ 400 300 0 0 == { left := 0 }

/-- The ambient safe-area insets (zero outside a window). Provided per window
and refreshed on `windowSafeAreaChanged`/resize/scale events; dynamic, so
only actual readers recompose when system bars move. -/
initialize LocalWindowInsets : CompositionLocal WindowInsets ← compositionLocalOf {}

/-- The window's text stack: the shared `FontStore` and the renderer text
engine both created by `bootstrap`. Consumed by `Material.Text` (and M11's
`TextField`) to build `TextLayout`s. -/
structure TextContext where
  /-- Shared font cache (bundled family + system fallbacks). -/
  fontStore : FontStore
  /-- The window's renderer text engine (atlas-cached, incremental). -/
  textEngine : Sdl.Ttf.TextEngine

/-- The ambient window text stack (`none` outside a window). Static — a window
never swaps its font store or text engine. Provided by `WindowContext.wrapContent`.
Mirrors an internal platform local rather than public API. -/
initialize LocalTextContext : CompositionLocal (Option TextContext) ←
  return { id := ← freshId, defaultValue := none, isStatic := true,
           eq := fun _ _ => true }

/-- One entry of the window's overlay registry (M10): an independent
composition subtree the root's overlay host composes *after* the main
content, measured with window constraints — drawn on top, hit-tested first.
Registered/unregistered by `Popup`/`Dialog` (`Compose.Ui.Overlay`). Mirrors
the popup-layout entries `androidx.compose.ui.window.Popup` hangs off the
owner. -/
structure OverlayEntry where
  /-- Process-unique identity (registry removal, `keyed` group identity). -/
  id : Nat
  /-- The entry's layer content; refreshed by the owning composable every
  composition so the host always composes the latest capture. -/
  content : IO.Ref (Composable Unit)
  /-- Bumped by the owner whenever `content` is refreshed, so the host layer
  recomposes (the owner's recomposition propagates into the overlay). -/
  revision : MutableState Nat
  /-- `CompositionLocal` scope captured at the owner's call site — the layer
  composes under these, so overlay content sees the theme/density/scheduler
  of where the `Popup` sits, like Compose's popup composition inheriting the
  parent `CompositionContext`. -/
  locals : IO.Ref LocalMap

instance : Nonempty OverlayEntry :=
  ⟨{ id := 0
     content := Classical.choice inferInstance
     revision := Classical.choice inferInstance
     locals := Classical.choice inferInstance }⟩

/-- An app-level key handler registered by an overlay (M10): `capture`
handlers run *before* focused-node routing (a focusable popup grabs the
keyboard while open), the rest run after it but before the Tab/Esc fallbacks
(Esc-dismisses-popup wins over Esc-clears-focus). Innermost overlay first =
last registered consulted first. -/
structure OverlayKeyHandler where
  /-- The registering overlay's id. -/
  id : Nat
  /-- Run before focused-node key routing. -/
  capture : Bool
  /-- `true` consumes the event. -/
  handler : KeyEvent → IO Bool

instance : Inhabited OverlayKeyHandler :=
  ⟨{ id := 0, capture := false, handler := fun _ => pure false }⟩

/-- Per-window state owned by the app shell (see the module docstring).
Create via `Compose.bootstrap`; the record itself is plumbing — composables
should prefer the dedicated locals (`LocalDensity`, `LocalScheduler`). -/
structure WindowContext where
  /-- The SDL window. -/
  window : Sdl.Window
  /-- The rendering backend all drawing targets (`SdlBackend` by default; the
  GPU backend on real drivers when selected — see `AppConfig.backend`). -/
  backend : Draw.RenderBackend
  /-- Density derived from `Window.displayScale`; a `MutableState` so the
  root provider recomposes when the scale changes. -/
  densityState : MutableState Density
  /-- Safe-area insets from `Window.getSafeArea`; a `MutableState` so
  `LocalWindowInsets` readers recompose when system bars/cutouts move
  (refreshed by `refreshSafeArea` on safe-area/resize/scale events). -/
  safeAreaState : MutableState WindowInsets
  /-- Root of the layout tree (the composition's applier root). -/
  root : LayoutNode
  /-- The window's coroutine scheduler (wake = SDL user event push). -/
  scheduler : Scheduler
  /-- The window's text stack (font store + renderer text engine), created by
  `bootstrap` and provided to composition as `LocalTextContext`. -/
  textContext : TextContext
  /-- The composition, installed by `bootstrap` right after creation (the
  content wrapper needs the context, so the knot is tied through this cell —
  always `some` once `bootstrap` returns). -/
  compositionCell : IO.Ref (Option Composition)
  /-- A frame is scheduled: recompose/remeasure/redraw on the next loop pass.
  Set by the invalidation hooks, event dispatch, and `requestFrame`. -/
  needsFrame : IO.Ref Bool
  /-- The loop exits at the next iteration once set. -/
  quitRequested : IO.Ref Bool
  /-- Frames presented so far (observability; the smoke cap counts loop
  passes — see `Compose.runLoop`). -/
  framesRendered : IO.Ref Nat
  /-- M6's input hook: every event the shell does not consume (pointer, key,
  text, …) is offered here; `true` means handled. M5 installs the default
  `fun _ => pure false`; M6 replaces it with pointer/key dispatch into the
  tree. -/
  inputSink : IO.Ref (Sdl.Event → IO Bool)
  /-- The registered SDL user-event type used solely to wake the sleeping
  loop (`Scheduler.wake`); carries no payload and is dropped on receipt. -/
  wakeEvent : Sdl.EventType
  /-- M10's overlay registry, in registration order (draw order; reverse hit
  order). A state so the overlay host recomposes on register/unregister;
  never-equal policy — entries carry no useful equality. -/
  overlays : MutableState (Array OverlayEntry)
  /-- Overlay key handlers (see `OverlayKeyHandler`); consulted by the input
  router. -/
  keyHandlers : IO.Ref (Array OverlayKeyHandler)
  /-- The window's `FocusManager`, installed by `installInput` (M14b): the
  bridge `FocusRequester`s use to reach focus from composition. -/
  focusManager : IO.Ref (Option FocusManager)
  /-- Modal-overlay focus lifecycle hook `(scope id) (opening)`: called by a
  modal `Dialog` when it registers (`true`) / unregisters (`false`).
  `installInput` points it at the `FocusManager` (scope Tab traversal, restore
  prior focus); the default is a no-op (headless compositions with no input
  pipeline). -/
  modalFocusHook : IO.Ref (Nat → Bool → IO Unit)

/-- The ambient `WindowContext` (`none` outside a window). Treat as opaque
plumbing — for framework internals (overlays in M10, IME in M6), not app
code. Mirrors `LocalView`-ish internals rather than a public API. -/
initialize LocalWindowContext : CompositionLocal (Option WindowContext) ←
  return { id := ← freshId, defaultValue := none, isStatic := true,
           eq := fun _ _ => true }

namespace WindowContext

/-- The window's composition (throws before `bootstrap` finishes tying the
knot). -/
def composition (ctx : WindowContext) : IO Composition := do
  match ← ctx.compositionCell.get with
  | some c => return c
  | none => throw (IO.userError "Compose: WindowContext has no composition yet")

/-- The current density. -/
def density (ctx : WindowContext) : IO Density :=
  ctx.densityState.get

/-- Recompute the safe-area insets from the live window and publish them
(readers recompose only on an actual change). Called by `bootstrapWindow`
once and by event dispatch on `windowSafeAreaChanged`/resize/scale-change.
Best effort: a driver without safe-area support keeps the current (zero)
insets. -/
def refreshSafeArea (ctx : WindowContext) : IO Unit := do
  try
    let safe ← ctx.window.getSafeArea
    let (ww, wh) ← ctx.window.getSize
    let pixelDensity ← ctx.window.pixelDensity
    let density ← ctx.densityState.get
    ctx.safeAreaState.set
      (WindowInsets.ofSafeArea safe ww wh pixelDensity density.density)
  catch _ => pure ()

/-- The raw SDL renderer of an `.sdlRenderer`-backed window — the test and
screenshot escape hatch (`readPixels`, `coordinatesToWindow`). Throws for a
GPU-backed window. -/
def sdlRenderer (ctx : WindowContext) : IO Sdl.Renderer := do
  match ctx.backend.sdlRenderer? with
  | some r => return r
  | none => throw (IO.userError
      "Compose: window is not backed by an SDL renderer (GPU backend has no readback path)")

/-- Schedule a frame: the next loop pass recomposes/remeasures/redraws.
Idempotent. Mirrors `Owner.onRequestMeasure`/`invalidate` scheduling. -/
def requestFrame (ctx : WindowContext) : IO Unit :=
  ctx.needsFrame.set true

/-- Ask the loop to exit (honored at the next iteration). -/
def requestQuit (ctx : WindowContext) : IO Unit :=
  ctx.quitRequested.set true

/-- Append an overlay entry (drawn on top of all earlier ones). The state
write recomposes the overlay host. -/
def registerOverlay (ctx : WindowContext) (e : OverlayEntry) : IO Unit :=
  ctx.overlays.modify (·.push e)

/-- Remove the overlay entry with the given id. -/
def unregisterOverlay (ctx : WindowContext) (id : Nat) : IO Unit :=
  ctx.overlays.modify (·.filter (·.id != id))

/-- Register an overlay key handler (innermost = last registered wins the
first look; see `OverlayKeyHandler`). -/
def registerKeyHandler (ctx : WindowContext) (h : OverlayKeyHandler) : IO Unit :=
  ctx.keyHandlers.modify (·.push h)

/-- Remove the key handler registered under `id`. -/
def unregisterKeyHandler (ctx : WindowContext) (id : Nat) : IO Unit :=
  ctx.keyHandlers.modify (·.filter (·.id != id))

/-- A non-skippable restart scope for the window root, so the density read
below re-runs the providers when the scale changes (reads at the composition
root would otherwise have no scope to invalidate). -/
private partial def rootRestartable (body : Composable Unit) : Composable Unit := fun c => do
  let scope ← c.startRestartGroup (stringKey "Compose.WindowContext.root")
  if ← c.shouldSkip scope (argsChanged := false) then
    c.skipToGroupEnd
  else
    body.run c
  c.endRestartGroup scope ((rootRestartable body).run c)

/-- Wrap app content with the window's ambient providers: `LocalDensity`
(re-provided when the display scale changes), `LocalWindowInsets` (safe-area
edges), `LocalScheduler` (effects), and `LocalWindowContext`. The shell
composes this, never raw content. -/
def wrapContent (ctx : WindowContext) (content : Composable Unit) : Composable Unit :=
  rootRestartable do
    let d ← ctx.densityState.get
    let insets ← ctx.safeAreaState.get
    CompositionLocalProvider LocalWindowContext (some ctx) <|
      CompositionLocalProvider LocalTextContext (some ctx.textContext) <|
        CompositionLocalProvider LocalScheduler (some ctx.scheduler) <|
          CompositionLocalProvider LocalWindowInsets insets <|
            CompositionLocalProvider LocalDensity d content

end WindowContext

/-- Pad by the window's safe-area insets, so content stays clear of status
bars, display cutouts, and gesture zones (a no-op on desktop, where the
insets are zero). Reads `LocalWindowInsets`, hence `Composable`:
`Box (modifier := ← Modifier.safeAreaPadding) content`. Mirrors
`Modifier.safeDrawingPadding()`. -/
def Modifier.safeAreaPadding (m : Modifier := {}) : Composable Modifier := do
  let insets ← LocalWindowInsets.current
  return m.padding (left := some insets.left) (top := some insets.top)
    (right := some insets.right) (bottom := some insets.bottom)

end Compose
