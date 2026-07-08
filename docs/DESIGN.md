# compose-ui architecture

Settled design for a Jetpack-Compose-style declarative UI framework in Lean 4,
rendered with SDL3 via [lean-sdl3](https://github.com/philnguyen/lean-sdl3).
Read together with `AGENTS.md` (conventions) and `docs/ROADMAP.md` (milestones).
Implementation subagents: follow this document exactly; deviations require
orchestrator sign-off — if you believe a decision is wrong, say so in your
report instead of silently diverging.

Product decisions (settled with the project owner):
- Dependency on lean-sdl3 is a **pinned git require** (bump deliberately).
- Popups/dialogs/dropdowns are **in-window overlays**; the window abstraction
  must not preclude real multi-window later (no global "the window" singletons
  below `Compose/Ui/App`).
- **Full-ambition animation system**: springs, `Animatable` with velocity and
  interruption, transitions, `AnimatedVisibility`, infinite transitions.
- **Material-lite default theme**: light/dark color schemes, typography scale,
  shape system, hover/pressed/focused states.

## Layering

Mirrors Compose's runtime/ui/foundation/material split; each layer only
imports layers above it in this list:

| Layer | Modules | Contents |
|---|---|---|
| core | `Compose/Core/*` | `Color`, geometry (`Offset`/`Size`/`Rect`/`RoundRect`), `Dp`/`Sp`/`Density` — pure, SDL-free |
| runtime | `Compose/Runtime/*` | state, slot tree, composer, effects, coroutines, frame clock, `composable` macro — **UI-free and SDL-free**, testable with a test applier |
| animation | `Compose/Animation/*` | easing, springs, specs, `Animatable`, `animate*AsState`, `Transition` — depends on runtime only |
| ui | `Compose/Ui/*` | constraints/layout, modifiers, draw (tessellation + SDL renderer backend), text, input, window/app loop, overlays |
| foundation | `Compose/Foundation/*` | `Row`/`Column`/`Box`/`Spacer`, scroll, lazy lists, gesture detectors, interaction sources |
| material | `Compose/Material/*` | theme + widget set |
| demos | `Demos/*` | the seven 7GUIs tasks + gallery |

## Threading model

Everything UI-related runs on the OS main thread: SDL video/render/events are
main-thread-only (lean-sdl3 guarantees `main` runs there). Consequences:
- No snapshot MVCC is needed. Compose's snapshot system exists for
  multi-threaded isolation; single-threaded read-tracking gives observably
  equivalent behavior. We implement **read observation + targeted
  invalidation** without snapshots (documented deviation).
- Background work uses `Task`/`IO.asTask` for *pure* computation only; results
  marshal back by pushing an SDL user event (wakes the event loop) and
  completing a pending continuation on the main thread.
- Effects/animations are **cooperative coroutines** on a main-thread
  scheduler, not OS threads.

## Runtime

### State (`Compose/Runtime/State.lean`)

```lean
MutableState α          -- identity-carrying mutable cell
mutableStateOf  [BEq α] (init : α) : IO (MutableState α)   -- structural-equality skip policy
mutableStateOfAlwaysNotify (init : α) : IO (MutableState α) -- never-equal policy
MutableState.get    : IO α        -- registers a read with the ambient observer
MutableState.set    : α → IO Unit -- no-op if equal per policy; else invalidates dependents
MutableState.modify : (α → α) → IO Unit
derivedStateOf [BEq α] (compute : IO α) : IO (DerivedState α)
```

Read observation: a module-global observer stack
`initialize readObserver : IO.Ref (Array (StateId → IO Unit))`. Pushing an
observer while running a recomposition scope / measure pass / draw pass
records which states were read; `set` walks the state's dependent list and
invalidates (recompose scope, layout node remeasure, or window redraw
respectively). Registration is two-way: each dependent also records the states
it read, and unregisters them all before re-running (Compose semantics: a
scope observes exactly the states its **latest** run read). All of this is
plain single-threaded `IO.Ref` mutation.

`DerivedState` caches its value with a dirty flag; reading a dirty derived
state recomputes and re-registers. Its dependents are invalidated only if the
recomputed value differs (`BEq`).

### Slot storage (`Compose/Runtime/SlotVal.lean`)

Positional memoization stores heterogeneous values. `SlotVal` is an
`unsafeCast`-based dynamic box behind a safe opaque interface
(`opaque` + `@[implemented_by]`), with the soundness invariant documented:
*a slot is only read back at the same group key and slot index where it was
written, so the static type at read equals the type at write*. This is the
one audited unsafe module in the codebase; nothing else may use `unsafeCast`.

### Composer and slot tree (`Compose/Runtime/Composer.lean`)

The composition is a mutable tree of groups (no gap-buffer slot table — a
pointer tree is simple, correct, and fast enough; each group is an
`IO.Ref GroupData`):

```lean
structure GroupData where
  key      : UInt64                 -- source-position key (macro-injected) or user key hash
  slots    : Array SlotVal          -- remembered values, positional
  children : Array Group            -- sub-groups in order
  nodes    : Nat                    -- emitted-node count in this subtree (for applier indices)
  scope    : Option RecomposeScope  -- present on restartable groups
```

`Composer` holds: the applier, current group + child/slot cursors, a parent
stack, an `inserting : Bool` flag, the pending-invalidations set, and the
`CompositionLocal` scope map. The public monad:

```lean
abbrev Composable α := ReaderT Composer IO α
```

Group matching on recomposition is Compose's algorithm: at each child
position, if the next existing child's key matches, enter it; otherwise
search the remaining siblings for the key (handles conditional appearance and
`key`-driven reorder); missing → insert, leftovers at group end → dispose
(run rememberedObserver/effect disposals depth-first) and remove their
emitted nodes via the applier.

Core combinators (macro-generated code calls these; they are also the
explicit escape hatch):

```lean
withGroup     (key : UInt64) (body : Composable α) : Composable α
keyed         [Hashable κ] (k : κ) (body : Composable α) : Composable α
remember      (init : IO α) : Composable α
rememberKeyed [BEq κ] (k : κ) (init : IO α) : Composable α  -- re-init when k changes
emitNode      (create : IO N) (update : N → Composable Unit)
              (content : Composable Unit) : Composable Unit
```

### Applier abstraction (`Compose/Runtime/Applier.lean`)

```lean
structure Applier (N : Type) where
  root     : N
  insert   : (parent : N) → (index : Nat) → (child : N) → IO Unit
  remove   : (parent : N) → (index count : Nat) → IO Unit
  move     : (parent : N) → (from to count : Nat) → IO Unit
  onClear  : IO Unit
```

The runtime is parameterized over `N`; runtime tests instantiate a
`TestApplier` over a pure tree of labeled nodes and assert tree shapes after
recompositions. The UI layer instantiates `N := LayoutNode`.

### Recomposition (`Compose/Runtime/Recomposer.lean`)

`RecomposeScope` = the restartable unit: holds its group, a `run : IO Unit`
closure (re-invokes the composable body with the args of its latest
execution), and its read registrations. State writes mark scopes invalid and
enqueue them on the `Recomposer`; the app loop drains the queue once per
frame: sort pending scopes in tree order (parents first), skip scopes whose
ancestor already re-ran them, re-run each with cursors positioned at its
group. New invalidations raised *during* recomposition join the same drain
(bounded by an iteration cap with a loud error, like Compose).

### `composable` macro (`Compose/Runtime/Macro.lean`)

The Lean answer to Compose's compiler plugin. Two syntaxes:

```lean
composable def counter (label : String) : Composable Unit := do ...
```

The macro rewrites the definition to a restartable, skippable function:
1. Wraps the body in `startRestartGroup k` / `endRestartGroup` where
   `k : UInt64` is a hash of the fully-qualified name (stable at runtime —
   it's a compile-time literal).
2. Generates the skip check: if the scope is not invalidated and all args are
   unchanged (`BEq` per arg via a `SkipEq` helper class whose fallback
   instance is never-equal, so non-`BEq` args just disable skipping), skip the
   body and replay the group (advance cursors over it).
3. Stores `fun () => counter label composer'` in the scope so the recomposer
   can restart it in place.
4. **Control-flow keying**: traverses the do-block syntax and wraps the
   branches of `if`/`match` and the bodies of `for` with `withGroup k` where
   `k` hashes the def name + branch's source position (compile-time literal;
   stable for the process lifetime, which is all positional memoization
   needs). `for` bodies get positional sibling groups; identity across
   reorder requires explicit `keyed x.id do`.

Content lambdas (`(content : Composable Unit)` parameters) are values, not
defs; they participate via the groups of the call sites inside them. A
`composable fun` term syntax wraps lambda literals in a group the same way.

The runtime must be fully usable *without* the macro (explicit `withGroup` /
`remember`), so the macro milestone is pure sugar + skippability and can land
after the runtime core.

### Effects and coroutines (`Compose/Runtime/Effects.lean`, `Scheduler.lean`)

`UiTask α`: a CPS-based cooperative coroutine monad on the main-thread
scheduler with structured cancellation:

```lean
UiTask.delay (ms : UInt32) : UiTask Unit
UiTask.awaitFrame : UiTask UInt64            -- nanos, the frame clock
UiTask.await (t : Task α) : UiTask α         -- background Task; completion wakes the loop via user event
launch (t : UiTask Unit) : IO CancelToken
```

Composition-side effects mirror Compose exactly:

```lean
LaunchedEffect  [BEq κ] (k : κ) (block : UiTask Unit) : Composable Unit  -- relaunch on key change, cancel on leave
DisposableEffect [BEq κ] (k : κ) (block : IO (IO Unit)) : Composable Unit -- returns onDispose
SideEffect      (block : IO Unit) : Composable Unit  -- runs after successful application
rememberUpdatedState, rememberCoroutineScope analogs
```

Effect launch/dispose ordering matches Compose: disposals of removed groups
run before new launches, in depth-first order.

### CompositionLocal (`Compose/Runtime/Locals.lean`)

```lean
compositionLocalOf (default : α) : IO (CompositionLocal α)   -- dynamic: providers invalidate readers
staticCompositionLocalOf (default : α)                        -- static: providers recompose subtree
CompositionLocalProvider (local) (value) (content) : Composable Unit
CompositionLocal.current : Composable α
```

Provided values live in a persistent map carried on the composer and stored
in provider groups; reads register dependencies like state reads.

## UI layer

### Coordinates, density, HiDPI

All internal UI coordinates are **pixels** (`Float32` for draw, `Int32` for
layout). `Density.density` comes from `Window.displayScale`, re-read on
`windowDisplayScaleChanged`/`windowPixelSizeChanged` (full invalidate).
Mouse coordinates convert window→render space via
`Renderer.coordinatesFromWindow`. Public API is `Dp`-typed throughout.

### Layout (`Compose/Ui/Layout.lean`, `Constraints.lean`, `Node.lean`)

Compose's single-pass model:

```lean
structure Constraints where       -- pixels; maxWidth/maxHeight use `Constraints.infinity` sentinel
  minWidth maxWidth minHeight maxHeight : Int32

MeasurePolicy := Array Measurable → Constraints → IO MeasureResult
-- MeasureResult: chosen IntSize + a placement block that calls Placeable.placeAt
```

`LayoutNode`: mutable record (`IO.Ref` fields) — parent, children, modifier
chain, measure policy, cached measurement (size, last constraints), position,
dirty flags (`needsRemeasure`, `needsRelayout`, `needsRedraw`), and the
resolved modifier wrapper chain. Measurement short-circuits when constraints
are unchanged and the node isn't dirty. State reads inside measure/placement
blocks are observed and invalidate remeasure of exactly that node.
Remeasure requests walk up only while the parent's measurement depends on the
child's size (Compose's `requestRemeasure` propagation, simplified: propagate
until a node whose cached size survives remeasure, then relayout downward).

Modifier chain = `Array Modifier.Elem` folded (outermost first) into a
wrapper chain around the node's inner measurable, old-Compose
`LayoutNodeWrapper` style:

```lean
inductive Modifier.Elem
  | layout   (LayoutElem)      -- padding, size, offset, weight-data, align-data …
  | draw     (DrawElem)        -- background, border, drawBehind, alpha, clip
  | pointer  (PointerElem)     -- pointerInput handlers, hover, cursor shape
  | focus    (FocusElem)
  | semantics (SemanticsElem)  -- role/label, used by tests
```

`Modifier` is a struct wrapping the array; combinators append
(`Modifier.padding (all := 16) |>.background theme.surface |>.clickable onClick`).
`Dp` parameters resolve to px at measure time via the ambient density.

Standard layouts in foundation: `Row`/`Column` (Arrangement + Alignment +
`weight`), `Box` (contentAlignment, `matchParentSize`), `Spacer`. Weight
semantics match Compose: weighted children measured after unweighted, sharing
remaining space; `fill` flag controls min constraints.

### Drawing (`Compose/Ui/Draw/*.lean`)

Immediate mode per dirty frame: walk the tree once, emit into the SDL
renderer. No damage regions initially (full redraw when dirty; the tree is
small — revisit only if profiling says so).

`DrawScope` (a reader over renderer + transform/clip stacks):

```lean
drawRect / drawRoundRect / drawCircle / drawLine / drawArc
  (brush : Brush) (style : Fill | Stroke width) …
drawText (layout : TextLayout) (topLeft) (color)
clipRect (r : Rect) (body) ; clipRoundRect (rr) (body)
translate (o : Offset) (body) ; withAlpha (a) (body)
```

`Brush` = `solid Color` | `linearGradient` (vertex colors make gradients free).

**Anti-aliasing strategy** (SDL's 2D renderer has none): all curved/rounded
shapes are tessellated to triangle meshes with a **1 px feathered edge ring**
(outer ring vertices share position direction but alpha 0), drawn via
`Renderer.geometry`. Axis-aligned crisp rects use `fillRect` directly.
`Compose/Ui/Draw/Tessellate.lean` is **pure** (`Array Vertex × Array Int32`
out) and heavily `#guard`-tested: rounded-rect fill, rounded-rect stroke,
circle fill/stroke, arc stroke (for circular progress), line with width,
polygon clip of a circle against a round-rect (for bounded ripples).
Adaptive segment count: `⌈π/2 · r / 2px⌉` segments per corner, min 4.

**Clip stack**: rectangular clips compose by intersection onto SDL's single
clip rect (push/pop in `DrawScope`). `clipRoundRect` sets the rect clip of
the bounds AND passes the rrect down so tessellated draws inside can
geometrically clip (covers ripple-in-button; arbitrary content under rounded
clip degrades to rect clip — documented limitation, revisit with
render-to-texture masking only if a real use appears).

Draw order: node's draw modifiers (outer→inner: background under border
under content), then children in order (later = on top). Hit testing uses
the same order reversed.

### Text (`Compose/Ui/Text/*.lean`)

- `FontStore`: caches `Ttf.Font` per (family, weight?, px size). Font
  resolution: bundled default font (`assets/fonts/`, OFL-licensed, committed)
  with platform fallbacks appended via `addFallbackFont` where available.
  Sizes are device-px (dp/sp × density) so glyphs are crisp on HiDPI.
- `TextLayout`: wraps a `Ttf.Text` on the window's **renderer text engine**
  (atlas-cached, incremental). Created/updated by Text nodes; measurement via
  `Text.size`, wrapping via `setWrapWidth`; drawn with `drawRenderer`.
  Hit-testing/caret geometry via `subStringForPoint` / `subString` rects
  (drives TextField).
- `Compose/Material/Text.lean` `Text` composable: remembers a `TextLayout`,
  updates it on string/style change (state-read tracked), measure policy
  reports intrinsic size clamped to constraints.

### Input (`Compose/Ui/Input/*.lean`)

- **Pointer**: SDL mouse events → `PointerEvent` (position px, buttons,
  scroll delta, click count). Hit test from root (children reverse order,
  respecting clip bounds), producing a hit path; dispatch along the path with
  a `consumed` flag (simplified Compose consumption; tunnel/bubble = the
  standard down-then-up pass). Gesture detectors in foundation build on a
  per-pointer event stream delivered to `Modifier.pointerInput` coroutines:
  `detectTapGestures (onTap onDoubleTap onLongPress onPress)`,
  `detectDragGestures`, `detectHover` (enter/move/exit), wheel scroll.
  Double-click uses SDL's `clicks` field.
- **Hover & cursor**: hover path diffing produces enter/exit; a
  `Modifier.pointerHoverIcon` elem sets the system cursor (I-beam over
  text fields, hand over links); the topmost wins, restored on exit.
- **Focus** (`Focus.lean`): `FocusManager` with focused-node ref;
  `Modifier.focusable`; Tab/Shift-Tab traverse focusables in layout order;
  click-to-focus; focused node draws via `focused` interaction state; Esc
  clears. Key events route: focused node first, then up the ancestor chain,
  then app-level handlers.
- **Keyboard & IME**: focused TextField calls `Window.startTextInput`, sets
  `setTextInputArea` to the caret rect each frame it moves, consumes
  `textInput`/`textEditing` events; key repeat comes from SDL's `repeat` flag.
- **Interaction sources** (foundation): `InteractionSource` streams
  pressed/hovered/focused/dragged, driving Material state layers.

### Window, app loop, overlays (`Compose/Ui/App.lean`, `Window.lean`, `Overlay.lean`)

```lean
Compose.runApp (title : String) (size : IntSize) (content : Composable Unit)
  (config : AppConfig := {}) : IO UInt32
```

Owns: SDL init, window + renderer (+ text engine), density tracking, the
`Recomposer`, `Scheduler`, `FontStore`, root `LayoutNode`, overlay stack.
Per-window state lives in a `WindowContext` record provided to composition
via CompositionLocals — **no globals** (multi-window later just means several
contexts). The loop (power-friendly, dirty-driven):

1. Compute next wake: `min(scheduler deadline, animation frame?, ∞)`;
   `waitEventTimeout` that long (or poll when a frame is already scheduled).
2. Translate + dispatch all pending events (input, resize→remeasure,
   scale-change→rebuild density, close→quit, exposed→redraw).
3. Run due coroutines; if the frame clock has subscribers, tick it.
4. If anything invalid: drain recompositions → apply node changes →
   remeasure/relayout dirty nodes → draw → `present` (vsync-paced).
5. Honor `COMPOSE_MAX_FRAMES` env var (headless CI smoke, mirroring
   lean-sdl3's `SDL_LEAN_MAX_FRAMES`).

**Overlays**: `Popup (anchor-relative positioning, onDismiss, focusable)` and
`Dialog (scrim, Esc/click-outside dismiss)` compose their content into
overlay entries on the `WindowContext` (a state list). Each overlay is an
independent layout root measured with window constraints; input hit-tests
overlays top-down first; a dialog's scrim swallows everything below.
Anchor rects come from `Modifier.onGloballyPositioned` coordinates.

## Animation (`Compose/Animation/*.lean`)

Full-parity ambition, structured exactly like Compose:

- `Easing` (cubic-bézier: standard/accelerate/decelerate + custom), `#guard`
  tested against known curve values with tolerance.
- `AnimationSpec α`: `tween (durationMs delay easing)`, `spring (dampingRatio
  stiffness visibilityThreshold)` (closed-form under/critical/over-damped
  solutions, ported from `SpringSimulation`), `keyframes`, `repeatable` /
  `infiniteRepeatable` (restart/reverse), `snap`.
- `VectorConverter α`: Float/Dp/Offset/Size/IntOffset/Color (sRGB lerp —
  documented deviation from Compose's Oklab) ↔ `AnimationVector1D..4D`.
- `Animatable α`: current value + velocity, `animateTo (target, spec)` as a
  `UiTask` — interruption cancels the previous run and starts from current
  value+velocity; `snapTo`, bounds.
- `animateFloatAsState` / `animateDpAsState` / `animateColorAsState` /
  `animateOffsetAsState` — remember an `Animatable`, relaunch on target change.
- `Transition`: `updateTransition (targetState)`, per-property
  `Transition.animateFloat/Color/Dp` with per-segment specs;
  `InfiniteTransition`.
- `AnimatedVisibility (visible) (enter exit)`: fade/slide/expand/shrink
  combos; keeps content composed until exit finishes.

All animation is driven by `UiTask.awaitFrame`; the loop ticks the frame
clock only while subscribers exist, so an idle UI consumes no CPU.

## Material-lite (`Compose/Material/*.lean`)

- `Theme.lean`: `ColorScheme` (light + dark, Material3-ish roles: primary,
  onPrimary, surface, onSurface, surfaceVariant, outline, error, …),
  `Typography` (display/headline/title/body/label × size), `Shapes`
  (corner radii S/M/L). `MaterialTheme (colors typography shapes) (content)`
  provides them via CompositionLocals; `theme.colors.primary` style accessors.
- State layers instead of full ripple: hover/press/focus draw a
  `primary`-tinted overlay at Material alpha tokens, animated via
  `animateFloatAsState`; press adds a bounded expanding-circle ripple
  (tessellated, clipped to shape) — cheap but convincing.
- Widgets: `Surface`, `Text`, `Button` (filled/outlined/text), `IconButton`
  (vector-ish icons drawn with primitives), `Checkbox`, `RadioButton`,
  `Switch`, `Slider` (drag + click + arrow keys), `LinearProgressIndicator` +
  `CircularProgressIndicator` (arc), `TextField` (single-line, outlined:
  caret blink via frame clock, selection with mouse drag/shift-arrows/
  double-click word select, clipboard shortcuts, IME composition underline,
  horizontal auto-scroll, `isError` state), `DropdownMenu` +
  `ExposedDropdownMenuBox` (Flight Booker), `AlertDialog`, `Divider`,
  `Scrollbar` (desktop-style, draggable thumb, auto-hide).
- Foundation scroll: `Modifier.verticalScroll (rememberScrollState())` +
  wheel + scrollbar; `LazyColumn`-lite: composes only visible keyed items
  (needed by CRUD list; Cells builds its own 2-axis virtualization on the
  same primitives).

TextField's editing model (`Compose/Ui/Text/EditModel.lean`) is **pure**:
`TextFieldValue {text, selection : Range, composition : Option Range}` ×
`EditCommand` → new value, exhaustively `#guard`-tested (insert, delete
variants, word-jump, selection extension, UTF-8 boundaries, IME set/commit).

## The 7GUIs demos (`Demos/*.lean`)

One `lean_exe` each + a `gallery` launcher listing all seven. Each demo is a
faithful implementation of the task spec, kept as small and idiomatic as the
framework allows (they double as the framework's showcase):
Counter, TempConverter (bidirectional conversion, invalid-input highlighting),
FlightBooker (dropdown, date validation, conditional enable), Timer
(progress bar, live duration slider, frame-clock-driven), CRUD (name filter,
list selection, create/update/delete), CircleDrawer (canvas clicks, nearest-
circle hover, right-click → popup → dialog with diameter slider, undo/redo
stack), Cells (99×26 spreadsheet: 2-axis virtualized grid with sticky
headers, click-to-select, double-click/type-to-edit, formula language parsed
with a hand-rolled parser — `=SUM(A1:B5)`, references, ranges, arithmetic —
reactive recalculation via topological change propagation, cycle detection).
Cells' formula engine is pure and `#guard`-tested (parser, evaluator,
dependency graph, cycles).

## Performance rules

- Draw only when dirty; sleep on `waitEventTimeout` otherwise. Frame clock
  ticks only with subscribers. Target: idle = 0% CPU, interaction = solid
  60 fps (vsync) with frame time « 16 ms.
- FBIP discipline in hot paths: keep `Array`s uniquely referenced (build
  with `push`/`set!` linearly, no stray captures); the tessellator and event
  translation must not allocate per-frame beyond their output arrays.
- Cache: text layouts per node (invalidate on content/style/density change),
  fonts in `FontStore`, tessellation of static shapes in draw-modifier state
  keyed by (shape, size, brush).
- Recomposition skipping via `BEq` args; `remember` derived values.
- Debug overlay (`COMPOSE_DEBUG_OVERLAY=1`): fps + frame-time + recomposition
  counts via `Renderer.debugText`.

## Testing

- Pure logic: `#guard`/`example` immediately below definitions (geometry,
  tessellation vertices, easing/spring math within tolerance bounds, edit
  model, formula engine, constraint arithmetic, arrangement math).
- Runtime (`test/Tests/<Area>.lean`, registered in `test/Tests.lean`, headless
  via dummy drivers): composition/recomposition semantics on `TestApplier`
  (insertion/removal/moves/effect ordering), state invalidation targeting,
  layout trees (constraints in / sizes+positions out), pointer dispatch with
  synthetic events, focus traversal, TextField end-to-end editing, and
  **pixel assertions**: render known scenes, `readPixels`, assert colors at
  probe points (the lean-sdl3 test suite proves this works headless).
- Demo smoke in CI: every demo runs `COMPOSE_MAX_FRAMES=60` under dummy
  drivers on macOS + Linux.
- Env: `COMPOSE_TEST_GROUP=<Name>` runs one group (lean-sdl3 pattern).
- **UI test framework (milestone MT, before the demos)** — the
  `androidx.compose.ui.test` analog, built on the semantics `Modifier.Elem`:
  widgets publish semantics (testTag, role, text, states, value ranges,
  actions); `runComposeTest` boots a headless window with a controlled clock
  and exposes finders (`onNodeWithText`/`onNodeWithTag`/matchers), actions
  (`performClick`/`performTextInput`/`performKeyPress`/drag/scroll — all
  synthesized through the real input router so tests exercise the true event
  path), assertions (text/displayed/checked/disabled/focused/bounds), and
  `waitForIdle`/`advanceTimeBy`. The 7GUIs demos ship behavior tests written
  in this framework — demo development doubles as the framework's own
  validation. Raw pixel probes remain appropriate only where pixel output is
  itself the property under test.

## Conventions for implementation agents

- Read `AGENTS.md` first (naming, piping style, commit discipline).
- Every public declaration gets a doc comment; cite the Compose analog
  (e.g. "Mirrors `androidx.compose.foundation.layout.Row`") where one exists.
- Layer discipline is absolute: runtime never imports `Sdl`; ui never imports
  material. `#guard` tests land in the same commit as the definition.
- Build + test before reporting done: `lake build` clean (no warnings,
  no `sorry`), `SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test`.
