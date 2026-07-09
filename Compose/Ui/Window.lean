import Sdl
import Compose.Runtime.Recomposer
import Compose.Runtime.LaunchedEffect
import Compose.Runtime.Macro
import Compose.Ui.Node
import Compose.Ui.Text.Fonts
import Compose.Ui.Text.Paragraph

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
  /-- The renderer all drawing targets. -/
  renderer : Sdl.Renderer
  /-- Density derived from `Window.displayScale`; a `MutableState` so the
  root provider recomposes when the scale changes. -/
  densityState : MutableState Density
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
(re-provided when the display scale changes), `LocalScheduler` (effects), and
`LocalWindowContext`. The shell composes this, never raw content. -/
def wrapContent (ctx : WindowContext) (content : Composable Unit) : Composable Unit :=
  rootRestartable do
    let d ← ctx.densityState.get
    CompositionLocalProvider LocalWindowContext (some ctx) <|
      CompositionLocalProvider LocalTextContext (some ctx.textContext) <|
        CompositionLocalProvider LocalScheduler (some ctx.scheduler) <|
          CompositionLocalProvider LocalDensity d content

end WindowContext

end Compose
