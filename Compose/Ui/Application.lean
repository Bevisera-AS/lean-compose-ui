module

public import Compose.Ui.App
public meta import Compose.Ui.App

public section

namespace Compose

/-!
# Declarative multi-window (`Compose/Ui/Application.lean`)

`Compose.application` runs an *app-level composition* in which `Window` and
`DialogWindow` composables declare real OS windows — state-driven, like
Compose for Desktop's `application { Window(...) }`:

```lean
def main : IO UInt32 := Compose.application do
  let isOpen ← remember (mutableStateOf true)
  if ← isOpen.get then
    Window "hello" 400 300 do ...
```

The content composes under a restartable root scope (`applicationRoot`), so
the state reads in a plain do-block like the one above recompose the
app-level composition when handlers write them — opening and closing windows
state-driven, no `composable def` needed at the root.

The app-level composition emits no layout nodes (emitting one throws — put
widgets inside a `Window`). Each `Window` creates a full `WindowContext` via
an effect on first composition, disposes it on leave, and updates
title/size on parameter change. **One** main loop drives every live window:
events route by `Sdl.Event.windowId` to the owning window's dispatch, one
shared `Scheduler` (and wake event) serves all windows, and the loop keeps
the single-window contract — dirty-driven, wake deadline `0` iff any window
needs a frame, scheduler deadline otherwise, idle cap else; idle = 0 % CPU.

The application exits when no windows remain (the composition has settled at
least once by construction — `bootstrapApplication` composes before the loop
starts) or when the action returned by `exitApplication` runs.
-/

/-- One live window of a running application: the routing id, its context,
render config, and the close-request hooks the loop consults. Managed by the
`Window` composable's effects; the loop only reads the registry. -/
structure WindowEntry where
  /-- The SDL window id events are routed by. -/
  id : Sdl.WindowId
  /-- The window's full per-window state (composition, renderer, …). -/
  ctx : WindowContext
  /-- Render config (`clearColor`, renderer choice, …) for `renderFrame`. -/
  config : AppConfig
  /-- Latest `onCloseRequest` handler (refreshed every composition);
  returning `true` closes the window. -/
  onClose : IO.Ref (IO Bool)
  /-- Close the window declaratively (flips the composable's internal
  closed latch; the disposal effect does the actual teardown). -/
  close : IO Unit

/-- A running application: the shared scheduler/wake event, the live-window
registry, and the app-level composition's dirty/exit flags. Created by
`bootstrapApplication`; reaches composables as `LocalApplication`. Mirrors
`androidx.compose.ui.window.ApplicationScope`. -/
structure ApplicationScope where
  /-- The one scheduler every window's effects and animations run on
  (its wake pushes the shared SDL user event). -/
  scheduler : Scheduler
  /-- The registered SDL user-event type that wakes the sleeping loop. -/
  wakeEvent : Sdl.EventType
  /-- Live windows, in creation order. -/
  windows : IO.Ref (Array WindowEntry)
  /-- The app-level composition needs a drain (a `Window` appeared/left or
  changed parameters). -/
  dirty : IO.Ref Bool
  /-- The loop exits at the next iteration once set (`exitApplication`). -/
  exitRequested : IO.Ref Bool
  /-- The app-level composition, installed by `bootstrapApplication` right
  after creation (always `some` once it returns). -/
  compositionCell : IO.Ref (Option Composition)

/-- The ambient `ApplicationScope` (`none` outside `Compose.application`).
`Window`/`DialogWindow` require it; `exitApplication` reads it. -/
initialize LocalApplication : CompositionLocal (Option ApplicationScope) ←
  return { id := ← freshId, defaultValue := none, isStatic := true,
           eq := fun _ _ => true }

namespace ApplicationScope

/-- Ask the application loop to exit (honored at the next iteration),
regardless of remaining windows. -/
def exit (app : ApplicationScope) : IO Unit :=
  app.exitRequested.set true

/-- The app-level composition (throws before `bootstrapApplication` finishes
tying the knot). -/
def composition (app : ApplicationScope) : IO Composition := do
  match ← app.compositionCell.get with
  | some c => return c
  | none => throw (IO.userError "Compose: ApplicationScope has no composition yet")

/-- Whether the loop should stop: exit was requested, or no windows remain
(the composition has settled at least once by the time this is consulted). -/
def done (app : ApplicationScope) : IO Bool := do
  if ← app.exitRequested.get then return true
  return (← app.windows.get).isEmpty

end ApplicationScope

/-- The vsync interval each **vsync-requesting** window's renderer should carry
under the single-pacer policy, in registry order (`none` = a window that opted
out of vsync, left untouched).

One vsynced `present` blocks to the next vblank; with every window vsynced, the
loop's sequential present pass serializes those waits and N animating windows
each run at ~fps/N. Instead the *first* vsync-requesting window paces (`1`) and
the rest present immediately (`0`): the single vsynced present paces the whole
loop at the display refresh, at the cost of possible tearing on the non-pacer
windows. Single-window apps are unaffected — their one window is the pacer. -/
def vsyncTargets (wantsVSync : Array Bool) : Array (Option Int32) := Id.run do
  let mut chosen := false
  let mut out := #[]
  for w in wantsVSync do
    if w then
      out := out.push (some (if chosen then 0 else 1))
      chosen := true
    else
      out := out.push none
  return out

-- One pacer among the vsync windows; opt-out windows (false) are never touched.
#guard vsyncTargets #[true, true, true] == #[some 1, some 0, some 0]
#guard vsyncTargets #[false, true, true] == #[none, some 1, some 0]
#guard vsyncTargets #[false, false] == #[none, none]
-- Single vsync window is itself the pacer (no behavior change for one window).
#guard vsyncTargets #[true] == #[some 1]
-- Re-election after the pacer (index 0) closes: a survivor takes over.
#guard vsyncTargets #[true, false] == #[some 1, none]
#guard vsyncTargets (#[true, true].eraseIdx! 0) == #[some 1]

/-- Re-elect the single vsync pacer across the live windows (`vsyncTargets`):
apply each vsync-requesting window's target to its renderer, leaving opt-out
windows alone. Idempotent — run on every window open/close so the pacer role
moves to a survivor when the current pacer leaves. `setVSync` is best-effort
(drivers may reject it; the loop still functions, just without pacing). -/
def electVSyncPacer (app : ApplicationScope) : IO Unit := do
  let ws ← app.windows.get
  for (e, t) in ws.zip (vsyncTargets (ws.map (·.config.vsync))) do
    if let some target := t then
      try e.ctx.backend.setVSync target catch _ => pure ()

/-- The action that exits the enclosing `Compose.application` (safe to call
from handlers/effects). Throws when composed outside one. Mirrors
`ApplicationScope.exitApplication`. -/
def exitApplication : Composable (IO Unit) := do
  match ← LocalApplication.current with
  | some app => return app.exit
  | none => throw (IO.userError
      "Compose: exitApplication needs an application (run via Compose.application)")

/-- Restartable root of the app-level composition: state reads in plain
do-block content (`for id in ← windows.get`, `if ← isOpen.get then
Window …`) are tracked by this scope, so handler writes recompose the
application — creating/disposing windows — without `composable def` at the
call site. The app-level analog of the window root's restart scope. -/
composable def applicationRoot (content : Composable Unit) : Composable Unit :=
  content

/-- Applier of the app-level composition: windows are effects, not nodes, so
inserting a node here is a bug — a widget composed outside a `Window` throws
a clear error instead of silently vanishing. -/
private def appApplier (root : LayoutNode) : Applier LayoutNode where
  root
  insert _ _ _ := throw (IO.userError
    "Compose.application: compose widgets inside a Window — the app-level \
     composition hosts only windows")
  remove _ _ _ := pure ()
  move _ _ _ _ := pure ()

/-- Create the shared scheduler/wake event and compose `content` at the app
level (under `LocalApplication` + `LocalScheduler`) — `Window` effects have
created their windows by the time this returns, so the emptiness-exit rule
is meaningful immediately. Everything `stepApplication` needs, without
entering the loop. Main thread only. -/
def bootstrapApplication (content : Composable Unit) : IO ApplicationScope := do
  initVideo
  let some wakeEvent ← Sdl.registerEvents 1
    | throw (IO.userError "Compose: SDL_RegisterEvents exhausted user event types")
  let scheduler ← Scheduler.create
    (wake := do let _ ← Sdl.pushUserEvent wakeEvent; pure ())
    (clock := Sdl.getTicksNS)
  let app : ApplicationScope :=
    { scheduler, wakeEvent
      windows := ← IO.mkRef #[]
      dirty := ← IO.mkRef true
      exitRequested := ← IO.mkRef false
      compositionCell := ← IO.mkRef none }
  let comp ← Composition.create (appApplier (← LayoutNode.create))
    (CompositionLocalProvider LocalApplication (some app) <|
      CompositionLocalProvider LocalScheduler (some scheduler) <|
        applicationRoot content)
  comp.setOnInvalidate (app.dirty.set true)
  app.compositionCell.set (some comp)
  return app

/-- Route one SDL event: `quit` exits the application, the shared wake user
event just ends a wait, app-lifecycle events (which carry no window id)
broadcast to every window, and everything else goes to the window
`Sdl.Event.windowId` names — `windowCloseRequested` to that window's
`onCloseRequest` (returning `true` closes it), the rest through the
single-window `dispatchEvent`. Events for no/unknown windows are dropped. -/
def dispatchApplicationEvent (app : ApplicationScope) (event : Sdl.Event) : IO Unit := do
  match event with
  | .quit _ => app.exit
  | .user t _ =>
    if t == app.wakeEvent.val then pure () -- wake events exist only to end a wait
  | .terminating _ | .lowMemory _
  | .willEnterBackground _ | .didEnterBackground _
  | .willEnterForeground _ | .didEnterForeground _ =>
    -- App-lifecycle: every window pauses/resumes/drops caches through its
    -- own dispatch (and each window's `onLifecycle` hook fires).
    for e in ← app.windows.get do
      dispatchEvent e.ctx e.config event
  | _ =>
    let some wid := event.windowId | pure ()
    let some entry := (← app.windows.get).find? (·.id == wid) | pure ()
    match event with
    | .windowCloseRequested _ =>
      if ← (← entry.onClose.get) then entry.close
    | _ => dispatchEvent entry.ctx entry.config event

/-- Wait timeout for the next application pass, in ms: `0` when anything is
pending (app composition dirty, any window dirty, live frame clock), else
time to the shared scheduler's next deadline, else `idleCapMs` — the exact
single-window `wakeTimeoutMs` contract over all windows. -/
def applicationWakeTimeoutMs (app : ApplicationScope)
    (idleCapMs : UInt32 := idleWaitMs) : IO Int32 := do
  if ← app.dirty.get then return 0
  -- Paused (backgrounded) windows don't render, so their dirtiness and the
  -- frame clock only force an immediate pass for a window that will draw.
  let mut anyLive := false
  for e in ← app.windows.get do
    unless ← e.ctx.paused.get do
      anyLive := true
      if ← e.ctx.needsFrame.get then return 0
  if anyLive && (← app.scheduler.hasFrameWork) then return 0
  let cap := idleCapMs.toUInt64
  match ← app.scheduler.nextDeadline with
  | none => return Int32.ofNat cap.toNat
  | some d =>
    let now ← Sdl.getTicksNS
    if d ≤ now then return 0
    return Int32.ofNat (min cap ((d - now) / 1_000_000 + 1)).toNat

/-- One pass of the application loop: wait for events up to the computed
deadline, dispatch them all by window id, run due coroutines, tick the
shared frame clock if subscribed, drain the app composition when dirty
(creating/disposing windows through `Window` effects — main thread), and
render every dirty window. Returns `true` iff any frame was presented. -/
def stepApplication (app : ApplicationScope)
    (idleCapMs : UInt32 := idleWaitMs)
    (watch : Option LiveResizeWatch := none) : IO Bool := do
  -- The live-resize watch may render only while we're parked *inside* a
  -- pump call (see `armedPump` and its section in `Compose/Ui/App.lean`):
  -- every dispatch runs disarmed.
  let timeout ← applicationWakeTimeoutMs app idleCapMs
  if timeout != 0 then
    if let some e ← armedPump watch (Sdl.waitEventTimeout timeout) then
      dispatchApplicationEvent app e
  repeat
    match ← armedPump watch Sdl.pollEvent with
    | some e => dispatchApplicationEvent app e
    | none => break
  if ← app.exitRequested.get then return false
  let now ← Sdl.getTicksNS
  app.scheduler.runDue now
  -- The shared frame clock drives visible windows; when every window is
  -- paused (the whole app is backgrounded) it stops with them.
  let mut anyLive := false
  for e in ← app.windows.get do
    unless ← e.ctx.paused.get do anyLive := true
  if anyLive && (← app.scheduler.hasFrameWork) then
    app.scheduler.tickFrame now
    for e in ← app.windows.get do
      unless ← e.ctx.paused.get do
        if let some probe ← e.ctx.frameProbe.get then probe now
  if ← app.dirty.get then
    app.dirty.set false
    (← app.composition).drain
  -- Render over a snapshot; a window a sibling's effects just disposed is
  -- skipped by re-checking registry membership.
  let mut rendered := false
  for e in ← app.windows.get do
    if (← app.windows.get).any (·.id == e.id) then
      if (← e.ctx.needsFrame.get) && !(← e.ctx.paused.get) then
        renderFrame e.ctx e.config
        if (← e.ctx.presentGrace.get) > 0 then
          e.ctx.presentGrace.modify (· - 1)
          e.ctx.requestFrame
        rendered := true
  return rendered

/-- Run the application loop until `done` (exit requested / no windows
left) — or, when `maxPasses` is set, for that many passes (the
`COMPOSE_MAX_FRAMES` headless mode, idle wait shrunk to `cappedIdleWaitMs`
exactly like `runLoop`). -/
partial def runApplicationLoop (app : ApplicationScope)
    (maxPasses : Option Nat := none)
    (watch : Option LiveResizeWatch := none) : IO Unit := do
  let idleCap := if maxPasses.isSome then cappedIdleWaitMs else idleWaitMs
  go maxPasses idleCap
where
  go (remaining : Option Nat) (idleCap : UInt32) : IO Unit := do
    if ← app.done then return
    if remaining == some 0 then return
    let _ ← stepApplication app idleCap watch
    go (remaining.map (· - 1)) idleCap

/-- Run a Compose application: compose `content` at the app level — where
`Window`/`DialogWindow` declare OS windows — and drive the shared,
dirty-driven event loop until no windows remain or `exitApplication` fires.
Honors `COMPOSE_MAX_FRAMES=<n>` (exit 0 after n loop passes — headless CI).
Call from `main` (main thread only). Mirrors
`androidx.compose.ui.window.application`. -/
def application (content : Composable Unit) : IO UInt32 := do
  let app ← bootstrapApplication content
  let watch ← installLiveResizeWatch fun wid => do
    return (← app.windows.get).find? (·.id == wid) |>.map fun e => (e.ctx, e.config)
  let lifecycleWatch ← installLifecycleWatch do
    return (← app.windows.get).map fun e => (e.ctx, e.config)
  let maxPasses := (← IO.getEnv "COMPOSE_MAX_FRAMES").bind (·.toNat?)
  runApplicationLoop app maxPasses (watch := some watch)
  let _ ← Sdl.removeEventWatch lifecycleWatch
  watch.remove
  (← app.composition).dispose -- disposes any remaining windows via their effects
  return 0

/-! ## The `Window` composable -/

/-- Per-`Window` plumbing surviving recompositions: the latest content/locals
capture (the overlay-entry pattern — the window root always composes the
freshest closure), the close latch, and the created context. -/
structure WindowNode where
  /-- Latest content closure; refreshed every composition of the owner. -/
  contentRef : IO.Ref (Composable Unit)
  /-- Bumped per refresh so the window root recomposes with it. -/
  revision : MutableState Nat
  /-- `CompositionLocal` scope captured at the `Window` call site — window
  content resolves app-level providers (theme, …) through it. -/
  locals : IO.Ref LocalMap
  /-- Latest `onCloseRequest` (shared with the loop via `WindowEntry`). -/
  onClose : IO.Ref (IO Bool)
  /-- The default-close latch: set by a close request the handler approved;
  the composable then composes nothing until it leaves and re-enters. -/
  closed : MutableState Bool
  /-- The live context (`none` before creation / after disposal). -/
  ctxCell : IO.Ref (Option WindowContext)

private instance : Nonempty WindowNode :=
  ⟨{ contentRef := Classical.choice inferInstance
     revision := Classical.choice inferInstance
     locals := Classical.choice inferInstance
     onClose := Classical.choice inferInstance
     closed := Classical.choice inferInstance
     ctxCell := Classical.choice inferInstance }⟩

/-- Read the composer's current `CompositionLocal` scope (captured for the
window root). -/
private def captureLocals : Composable LocalMap := fun c => c.locals.get

/-- Compose `body` with `base` appended *under* the current scope: the
window's own providers (density, scheduler, …) win, and anything provided
around the `Window` call site (theme, `LocalApplication`, the parent's
`LocalWindowContext` fallback) resolves through the capture. -/
private def withBaseLocals (base : LocalMap) (body : Composable Unit) :
    Composable Unit := fun c => do
  let cur ← c.locals.get
  c.locals.set ⟨cur.entries ++ base.entries⟩
  tryFinally (body.run c) (c.locals.set cur)

/-- Root content of one declared window: recomposes when the owning `Window`
refreshes its capture (the revision read) and composes the latest content
over the captured call-site locals. Runs inside the window's own
composition, under `WindowContext.wrapContent`. -/
composable def windowRoot (node : WindowNode) : Composable Unit := do
  let _ ← node.revision.get
  let body ← node.contentRef.get
  let base ← node.locals.get
  withBaseLocals base body

/-- Shared implementation of `Window` and `DialogWindow` (see their
docstrings): effect-managed `WindowContext` lifecycle plus keyed effects for
title/size updates. -/
composable def windowImpl (dialog : Bool) (title : String) (width height : Dp)
    (onCloseRequest : IO Bool) (config : AppConfig)
    (content : Composable Unit) : Composable Unit := do
  let app? ← LocalApplication.current
  match app? with
  | none =>
    throw (IO.userError
      "Compose: Window/DialogWindow need an application (run via Compose.application)")
  | some app =>
    let parentCtx? ← LocalWindowContext.current -- DialogWindow's parent
    let node : WindowNode ← remember do
      pure { contentRef := ← IO.mkRef (pure () : Composable Unit)
             revision := ← MutableState.create 0
             locals := ← IO.mkRef .empty
             onClose := ← IO.mkRef (pure true)
             closed := ← MutableState.create false
             ctxCell := ← IO.mkRef none }
    if !(← node.closed.get) then
      -- Refresh the capture every composition (latest state closures/locals),
      -- then bump the revision so the window root recomposes with them.
      node.locals.set (← captureLocals)
      node.contentRef.set content
      node.onClose.set onCloseRequest
      node.revision.modify (· + 1)
      DisposableEffect 0 do -- create once, dispose on leave/close
        let ctx ← bootstrapWindow app.scheduler app.wakeEvent title width height
          (windowRoot node) config
        node.ctxCell.set (some ctx)
        if dialog then
          if let some parent := parentCtx? then
            -- Dummy/odd drivers may lack modal support; a plain window then.
            try
              ctx.window.setParent (some parent.window)
              ctx.window.setModal true
            catch _ => pure ()
        app.windows.modify (·.push
          { id := ← ctx.window.id, ctx, config
            onClose := node.onClose
            close := node.closed.set true })
        electVSyncPacer app -- a new window may join or displace the pacer
        return do
          node.ctxCell.set none
          if dialog then -- unset modal before teardown
            try
              ctx.window.setModal false
              ctx.window.setParent none
            catch _ => pure ()
          let wid ← ctx.window.id
          app.windows.modify (·.filter (·.id != wid))
          electVSyncPacer app -- closing the pacer re-elects a survivor
          (← ctx.composition).dispose
          ctx.backend.dispose
          ctx.window.hide -- SDL windows are finalizer-destroyed; vanish now
      DisposableEffect title do -- retitle on change (first run is a no-op)
        if let some ctx ← node.ctxCell.get then
          ctx.window.setTitle title
        return pure ()
      DisposableEffect (width, height) do -- resize only on parameter change
        if let some ctx ← node.ctxCell.get then
          -- Window-coordinate size (see `windowCoordSize`): identity on
          -- macOS/dummy, scaled on Windows where window coords are pixels.
          let scale ← ctx.window.displayScale
          let pixelDensity ← ctx.window.pixelDensity
          let (w, h) := (windowCoordSize width scale pixelDensity,
                         windowCoordSize height scale pixelDensity)
          let (cw, ch) ← ctx.window.getSize
          unless cw == w && ch == h do
            ctx.window.setSize w h
        return pure ()

/-- Declare an OS window from the app-level composition: created (with its
own composition, renderer, and input pipeline) when this call enters the
composition, disposed when it leaves — `if (← isOpen.get) then Window ...`
opens and closes a real window. Title and size follow the parameters on
recomposition (a user resize is not overridden until they change).
`onCloseRequest` runs on the window's close button: return `true` to close
(the default; the window then stays closed until the call leaves and
re-enters the composition) or `false` to keep it open — flip your own state
there for fully state-driven closing. `config.onCloseRequest` is ignored
here (this parameter wins). Mirrors `androidx.compose.ui.window.Window`. -/
def Window (title : String) (width height : Dp)
    (content : Composable Unit := pure ())
    (onCloseRequest : IO Bool := pure true) (config : AppConfig := {}) :
    Composable Unit :=
  windowImpl false title width height onCloseRequest config content

/-- `Window`, as a modal dialog of the window that composed it: the new OS
window is parented to the ambient `LocalWindowContext`'s window and marked
modal (both best-effort — drivers without modal support get a plain window;
modality is unset before disposal). Compose it from a window's content.
Mirrors `androidx.compose.ui.window.DialogWindow`. -/
def DialogWindow (title : String) (width height : Dp)
    (content : Composable Unit := pure ())
    (onCloseRequest : IO Bool := pure true) (config : AppConfig := {}) :
    Composable Unit :=
  windowImpl true title width height onCloseRequest config content

end Compose

end
