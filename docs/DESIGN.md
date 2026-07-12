# compose-ui architecture

Settled design for a Jetpack-Compose-style declarative UI framework in Lean 4,
rendered with SDL3 via [lean-sdl3](https://github.com/philnguyen/lean-sdl3).
Read together with `AGENTS.md` (conventions) and `docs/ROADMAP.md` (milestones).
Implementation subagents: follow this document exactly; deviations require
orchestrator sign-off — if you believe a decision is wrong, say so in your
report instead of silently diverging.

**Compose-inspired, not a port** (project-owner directive): this framework
does not aim for 1-1 API fidelity with Kotlin Compose. *Semantics* parity
matters — recomposition behavior, invalidation precision, animation feel,
widget quality. *API shape* does not: whenever a pattern or idiom makes more
sense in Lean (do-notation, named/default args, macros, typeclasses, pattern
matching, pipes), do it Lean's way. We optimize for Lean's ergonomics. Doc
comments still cite Compose analogs — for orientation, not as a contract.

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
| ui | `Compose/Ui/*` | constraints/layout, modifiers, draw (display-list IR; SDL renderer + SDL_GPU backends), text, input, window/app loop, overlays |
| foundation | `Compose/Foundation/*` | `Row`/`Column`/`Box`/`Spacer`, `Image`, scroll, lazy lists, gesture detectors, interaction sources |
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
mutableStateOf  [BEq α] (init : α) : StateInit (MutableState α)   -- structural-equality skip policy
mutableStateOfAlwaysNotify (init : α) : StateInit (MutableState α) -- never-equal policy
MutableState.get    : IO α        -- registers a read with the ambient observer
MutableState.set    : α → IO Unit -- no-op if equal per policy; else invalidates dependents
MutableState.modify : (α → α) → IO Unit
derivedStateOf [BEq α] (compute : IO α) : StateInit (DerivedState α)
```

The builders return `StateInit` — a deferred initializer that `remember` takes
directly and that composition will not auto-run, so a forgotten `remember`
(state silently resetting every recomposition — the compose-rules "remember
missing" lint) is a type error. Plain-`IO` contexts (state holders, tests, app
plumbing) use the `MutableState.create*`/`DerivedState.create` constructors.

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
remember      (init : StateInit α) : Composable α           -- IO initializers lift in
rememberKeyed [BEq κ] (k : κ) (init : StateInit α) : Composable α  -- re-init when k changes
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
dirty flags (`needsRemeasure`, `needsRelayout` — redraws are whole-frame,
scheduled via the window's `needsFrame`, so there is no per-node redraw
flag), and the resolved modifier wrapper chain. Measurement short-circuits when constraints
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
  | draw     (DrawElem)        -- background, border, shadow, drawBehind, alpha, clip
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

Immediate mode per dirty frame, split **record → execute**: the draw walk
runs once through `DrawScope` (a reader over transform/clip/alpha state) and
*records* a flat, backend-neutral **display list** (`DisplayList.lean` — the
role Skia's `Picture` plays for Compose); the window's **`RenderBackend`**
(`Backend.lean`) then executes it. No damage regions yet (full redraw when
dirty), but the groundwork exists: `Prim.bounds` / `DisplayList.bounds`
report conservative device-space damage bounds per prim and per frame
(`none` = unknown — an unclipped text run). Revisit only if profiling says so.

`DrawScope` ops (signatures unchanged by the split):

```lean
drawRect / drawRoundRect / drawCircle / drawLine / drawArc
  (brush : Brush) (style : Fill | Stroke width) …
drawPath (brush) (path : Path) (style : PathStyle)  -- .fill | .stroke (s : Stroke)
drawText (run : TextRun) (topLeft)          -- via TextLayout.draw
drawImage (img : ImageBitmap) (dst) (src := none) (sampling := .linear)
clipRect (r : Rect) (body) ; clipRoundRect (rr) (body) ; clipPath (path) (body)
translate (o : Offset) (body) ; withAlpha (a) (body)
withGraphicsLayer (bounds) (g : GraphicsLayerScope) (body)  -- group alpha + transform
withLayer (bounds) (alpha) (body)          -- its transform-free case
```

`Brush` = `solid Color` | `linearGradient` (vertex colors make gradients free).

**Vector paths** (`Path.lean`, `PathFill.lean`): a `Path` is an immutable
verb array (`moveTo/lineTo/quadTo/cubicTo/close`, absolute coordinates) plus
a `FillRule` (`nonZero`/`evenOdd`), built with the `Path.build` `StateM`
builder (rel variants, `arcTo` lowered to cubics with `k = 4/3·tan(θ/4)` —
not a verb — and `addRect/addOval/addRoundRect`). Fills tessellate through a
pure **band-sweep**: flatten (adaptive de Casteljau, tol 0.25 px, depth-capped)
→ winding-signed non-horizontal edges → cut the y range at every endpoint and
pairwise intersection (O(edges²) discovery — icon scale) → per band, sort
actives by x at the midline and emit one trapezoid per inside span → feather
1 px on each boundary segment's unfilled side (side classified by the exact
winding oracle `Path.contains`, which also pins the tessellator via the
`pathFillAgreesWithOracle` `#guard` corpus + runtime fuzz). Holes, both fill
rules, and self-intersection all fall out of the winding accumulation; the
worst numeric failure is a sliver band, not a crash. The mesh IS the path
rasterization on **both** backends (`ShapeSpec.pathFill` rides `Prim.shape`
and the node mesh cache; GPU `lowerShape` sends it to the mesh pipeline — a
stencil-cover GPU path is possible future work).

**Path strokes** (`PathStroke.lean`): `drawPath`'s `.stroke` carries a full
`Stroke` — width, `StrokeCap` (butt/round/square), `StrokeJoin`
(miter-with-limit/round/bevel), optional `(intervals, phase)` dashing.
Stroke-to-fill, Skia style: dashes split by pure arc length first
(`dashSplit`), then `strokeOutline` emits consistently-wound convex pieces
(one rect per segment, one wedge/arc fan per join, cap pieces) and the bag
fills through the same band sweep under non-zero — overlap at tight joins and
abutting dashes resolves by winding, interior seams get no feather, and a bad
join degrades to a local shape error, never a broken mesh.

**`clipPath`** sets the rectangular bounds clip AND exposes the path
(render-target coordinates, re-anchored per draw across `translate`); path
*fills* inside record `ShapeSpec.pathFillClipped` — the same sweep run over
both edge sets with two winding accumulators, so path-clipped fills are exact
on **both** backends (the `circleFillClipped` precedent; feather segments are
split where the two boundaries cross so the apron never paints outside the
clipped region). All other content under `clipPath` degrades to the bounds
clip, and a nested `clipPath` replaces the ambient path (innermost exact) —
both documented limitations of the recorder's flat clip state.

**SDL geometry snapping**: SDL's software rasterizer truncates
`RenderGeometry` vertices to integer coordinates internally, which turns the
tessellators' sub-pixel band seams into dropped/doubled pixel rows. The SDL
backend therefore rounds every mesh vertex to the nearest pixel after the
origin translation (`meshToGeometry`) — the closest integer approximation of
true pixel-center coverage, gap-free by construction, and measurably tighter
GPU↔SDL parity than raw truncation. The GPU backend keeps the exact
fractional mesh.

**Images** (`Image.lean`, `Foundation/Image.lean`): an `ImageBitmap` wraps an
`Sdl.Surface` converted once to `rgba32` **straight alpha** with a
process-unique `id` (`BEq` = handle identity — the texture-cache key on both
backends). `ImageBitmap.load` decodes BMP+PNG via SDL 3.4's `loadSurface`;
`ofPixels` generates bitmaps for tests/demos with no binary assets.
`Prim.image` carries the bitmap, an optional source rect, the destination
rect, and a `Sampling` (`nearest`/`linear`). The SDL backend draws through a
per-backend never-evicted texture cache (`createTextureFromSurface` on first
use — probe-tested under the dummy driver — then per-draw scale mode + alpha
mod); the GPU backend uploads on miss into a process-wide cache
(**premultiplied** `r8g8b8a8Unorm` staging via a one-time `readPixel` loop —
a bulk `Surface.pixels` binding upstream is the noted fast-follow) and draws
textured quads through the **layer pipeline** (its fragment — premultiplied
sample × alpha — is exactly an image draw; the glyph shader would bleed under
linear filtering), choosing a second linear/clamp-to-edge sampler per
command. Cropping content scales cut with the source rect, so no clip is
needed; under a rounded clip images degrade to the rect scissor (the same
documented story as meshes/glyphs). The `Image` composable measures to the
bitmap's intrinsic size clamped to constraints and places pixels per
`ContentScale` (`fit`/`crop`/`fillBounds`/`none`, pure `resolve` `#guard`s).
Parity in practice: nearest draws are byte-exact across backends; linear
disagrees by ≤ 1 channel step (both gated in `gpu-parity`).

**Transforms** (`graphicsLayer` — layer-boundary only, the Compose model):
`Affine` (2×3, column convention, `#guard`ed inverse/compose/mapRect) lives
in `Core/Geometry.lean`; `GraphicsLayerScope` (rotationZ°, scaleX/Y,
translation px, fractional `transformOrigin`, group alpha) resolves at record
time to `LayerProps { alpha, transform : Option Affine }` on `Prim.layer` —
content records **untransformed**, executors render it axis-aligned into a
texture at full quality and map only the composite (so SDL text and GPU SDF
quads never rasterize rotated; the cost is texture-sampled transformed
content). `Modifier.graphicsLayer` compares structurally, so animating a
parameter redraws without re-tessellating (meshes key on the untransformed
shape). Clip semantics: clips *inside* the layer bake into the texture and
rotate with it; *enclosing* clips are stripped from the recorded content and
scissor the composite instead (they are target-coordinate regions — they
apply where pixels land); enclosing *rounded* clips degrade to that rect
scissor. On SDL a transformed layer becomes a **real offscreen target**
(pooled 64 px-quantized `.target` textures; content on a transparent clear
yields premultiplied texels; `textureAffine` composites with
`.blendPremultiplied` and color+alpha mod as the group alpha — so
transformed layers get true group opacity on SDL too, and the clip tracker
resets across every `setTarget` since SDL clip state is per-target).
Untransformed alpha layers keep the SDL flatten. On the GPU the conjugated
transform rides `LayerEnc` and maps the composite quad's corners.
`Affine.snapComposite` picks the sampling: near-integer pure translations
snap to the grid and composite nearest (crisp text, byte-exact parity —
settled animations land here automatically); everything else places
fractionally through the linear sampler. **Hit testing is not transformed**
(documented on the modifier; `invert?` is ready for the follow-up). Parity in
practice: 90°/snapped composites are byte-exact across backends; fractional
angles differ only in bilinear edge phase (mean ≈ 1.3, gated).

**The IR**: each `Prim` (crisp `rect` / `shape` with a `ShapeSpec` +
optional cached mesh / raw `mesh` / `text` run / `image` / `layer` with
`LayerProps`) is stamped with a
`PrimState` — accumulated translation, resolved rect-clip intersection, the
innermost rounded clip, folded alpha — so executors need no stacks.
`ShapeSpec` holds the fully resolved tessellation inputs and doubles as the
per-node mesh-cache key (`LayoutNode.cachedMesh`).

**Backends** (selected per window via `AppConfig.backend` /
`COMPOSE_BACKEND=gpu|sdl`, default SDL):

- **`SdlBackend.lean`** — SDL_Renderer + CPU tessellation; works headless
  under the dummy video driver (all CI/tests run here). Anti-aliasing (SDL's
  2D renderer has none): curved/rounded shapes tessellate to triangle meshes
  with a **1 px feathered edge ring** (outer ring vertices alpha 0), drawn
  via `Renderer.geometry`; axis-aligned solid rects use `fillRect` directly.
  `Tessellate.lean` is **pure** and heavily `#guard`-tested (rounded-rect
  fill/stroke, circle fill/stroke, arc stroke, line, polygon clip of a circle
  against a round-rect for bounded ripples; adaptive `⌈π/2 · r / 2px⌉`
  segments per corner, min 4). Untransformed layers flatten by folding alpha
  (documented double-blend approximation, pinned by a pixel test);
  *transformed* layers render to real pooled offscreen targets and composite
  via `textureAffine` (see **Transforms**); elevation shadows
  tessellate as rings 3σ inward and outward of the silhouette whose vertex
  alphas sample the same analytic shadow function the GPU evaluates
  (`roundRectShadow`).
- **`GpuBackend.lean`** (SDL_GPU, GPUI-style SDF instancing; `Gpu/*.lean`) —
  a pure encoder (`Encode.lean`) lowers the list into per-pipeline buffers +
  a flat `DrawCmd` list: axis-aligned rounded geometry under solid/two-stop
  brushes → instanced **SDF quads** (analytic coverage, math `#guard`-twinned
  in `Sdf.lean`); arcs, angled lines, the clipped ripple, multi-stop
  gradients → the **mesh pipeline** reusing the same CPU tessellation as SDL;
  text → **glyph-atlas quads** from SDL_ttf's GPU engine, snapped once per
  run at the rounded run origin (the resize text-shimmer fix); `rrShadow` →
  instanced **analytic Gaussian shadows** (Evan Wallace's closed-form erf
  integral, twinned in `Sdf.lean`); `layer` prims → **real offscreen layer
  passes** (group opacity composites once — no double blend; a transform maps
  the composite quad's corners, nearest when `snapComposite` else linear),
  textures from a per-window pool (64 px-quantized, first-fit, trimmed after
  120 idle frames). One shared `Gpu.Device` per process; MSL shaders compiled at
  runtime; premultiplied blending with non-premultiplied vertex colors
  (interpolation matches SDL's). Clips are per-command integer scissors with
  SDL's exact floor/ceil expansion, plus an in-shader rounded mask on every
  quad-path instance — `PrimState.rounded` clips exactly on the GPU, and the
  bounded ripple renders as a masked circle quad instead of a clipped mesh.
  `Gpu.frameStats` mirrors `tessellationCount`: the last frame's draw-call /
  instance counts (pure `EncodeResult.stats`). No dummy-driver support, so it
  is never the test backend: the IR goldens cover it headless, and a real
  driver gates it locally via `scripts/smoke-gpu.sh` — `lake exe gpu-probe`
  (runtime facts + offscreen pixel asserts through the real renderer),
  `lake exe gpu-parity` (renders identical display lists through both
  backends and asserts shift-tolerant pixel-diff bounds per scene), then
  every demo. `makeBackend` falls back to SDL with a warning when no GPU
  device exists.

**Clip stack**: rectangular clips compose by pure intersection at record
time. `clipRoundRect` records the bounds clip AND (a) passes the rrect down
in local coordinates so shape-aware draws geometrically clip at record time
(covers ripple-in-button), and (b) stamps it in target coordinates on every
prim (`PrimState.rounded`) — the GPU backend clips quad-path content exactly
via the in-shader mask (mesh-fallback shapes and glyphs get the rectangular
scissor). On the SDL backend arbitrary content under a rounded clip degrades
to the rect clip — documented limitation.

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

Live resize: macOS/Windows run a modal loop *inside* step 1's pump, freezing
the app until mouse-up. An SDL event watch (armed only while the loop is
parked in the pump) runs steps 3–4 synchronously from within it — once per
actual size change, deduping the several events each drag tick posts — so
content reflows and timers/animations advance during the drag. A drag held
motionless posts no events, so nothing can advance until the next tick.
(A cosmetic content-lag wobble during the drag remains on both backends:
SDL's presents — renderer and SDL_GPU/Metal alike — are asynchronous with no
transactional-present hook, so frames land a beat behind the window frame;
fixing it needs SDL changes. Documented punt.)

**Overlays**: `Popup (anchor-relative positioning, onDismiss, focusable)` and
`Dialog (scrim, Esc/click-outside dismiss)` compose their content into
overlay entries on the `WindowContext` (a state list). Each overlay is an
independent layout root measured with window constraints; input hit-tests
overlays top-down first; a dialog's scrim swallows everything below.
Anchor rects come from `Modifier.onGloballyPositioned` coordinates.

### Multi-window (`Compose/Ui/Application.lean`)

```lean
Compose.application (content : Composable Unit) : IO UInt32
Window (title) (width height : Dp) (onCloseRequest : IO Bool := pure true)
  (config : AppConfig := {}) (content) : Composable Unit
DialogWindow (…same…)   -- parented + modal to the composing window
exitApplication : Composable (IO Unit)   -- the explicit-exit action
```

Compose-for-Desktop-style declarative windows (M15). `application` runs an
*app-level composition* whose applier hosts no layout nodes (emitting a
widget there throws); `Window` composables declare OS windows state-driven:
each creates a full `WindowContext` via `bootstrapWindow` in a
`DisposableEffect` on enter, disposes it on leave, and updates title/size
via keyed effects on parameter change. Window content composes in the
window's *own* composition; the app-level `CompositionLocal` scope is
captured at the call site and appended under the window's providers (the
overlay-entry pattern), so app-level theme flows in while per-window
ambients win. `onCloseRequest` returns whether to close (default `true`,
via an internal latch); `DialogWindow` additionally does
`setParent`/`setModal true` toward the ambient `LocalWindowContext` window
(best-effort — unset before disposal; drivers without reparenting get a
plain window).

**One** main loop (`stepApplication`/`runApplicationLoop`) drives all
windows over a live registry (`ApplicationScope.windows`): events route by
`Sdl.Event.windowId` to the owning window's `dispatchEvent`
(`windowCloseRequested` to its `onCloseRequest`); `quit` and the wake user
event are app-level. One **shared** `Scheduler` (and wake event) serves all
windows — a per-window split would buy nothing since wakes land in the one
SDL queue anyway. The single-window wake contract holds verbatim: timeout
`0` iff the app composition or any window is dirty or the frame clock has
subscribers, else the scheduler deadline, else the idle cap — idle stays
0 % CPU. The application exits when no windows remain (the composition
settles during `bootstrapApplication`, before the loop) or on
`exitApplication`; `COMPOSE_MAX_FRAMES` caps loop passes as in `runApp`.
`runApp` remains the single-window fast path on the same
`bootstrapWindow`/`step` machinery.

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
- Widgets: `Surface` (shape/border/`elevation` shadow; Menu/Dialog/Tooltip
  surfaces default to 3/6/2 dp), `Text`, `Button` (filled/outlined/text), `IconButton`
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
  fonts in `FontStore`, tessellation of static shapes per node keyed by
  (shape, size px, brush, density) — see the status note below.
- Recomposition skipping via `BEq` args; `remember` derived values.
- Debug overlay (`COMPOSE_DEBUG_OVERLAY=1`): fps + frame-time + recomposition
  counts via `Renderer.debugText`.

**Status (M14 perf audit).** Verified implemented: idle sleeps in
`waitEventTimeout` until an event/deadline (0% CPU; the 5 ms idle cap applies
only under `COMPOSE_MAX_FRAMES`); frame clock ticks only with subscribers;
root remeasure short-circuits O(1) when clean and dirty nodes re-measure in
place; text layouts diff-update and fonts memoize; scroll offsets re-measure
only the scrolled node; lazy windows recompose only on window shifts. The
audit's one gap is closed: the tessellation cache above is implemented —
each node's `background`/`border` mesh is cached in `LayoutNodeData.meshCache`
keyed by a `Draw.ShapeSpec` holding the tessellation's fully resolved inputs
(shape × size px × density fold into the `RoundRect`, the paint into the
`Brush`, border width × density into the stroke px), so size/shape/brush/density
changes invalidate by key inequality and static shapes tessellate once, not
per frame (`LayoutNode.cachedMesh`; asserted by the DrawCache test group via
the debug `Draw.tessellationCount`). Meshes store `Int32` indices — the form
`Renderer.geometry` consumes — so emission does no per-frame index
conversion. The formerly write-only per-node `needsRedraw` flag was deleted
rather than wired up: rendering clears the full backbuffer, so honoring it
would need a damage-region/layer redesign — revisit only if profiling shows
draw-side cost that the mesh cache doesn't cover.

## Testing

- Pure logic: `#guard`/`example` immediately below definitions (geometry,
  tessellation vertices, easing/spring math within tolerance bounds, edit
  model, formula engine, constraint arithmetic, arrangement math).
- Runtime (`test/ComposeTests/<Area>.lean`, registered in
  `test/ComposeTests.lean`, headless
  via dummy drivers): composition/recomposition semantics on `TestApplier`
  (insertion/removal/moves/effect ordering), state invalidation targeting,
  layout trees (constraints in / sizes+positions out), pointer dispatch with
  synthetic events, focus traversal, TextField end-to-end editing, and
  **pixel assertions**: render known scenes, `readPixels`, assert colors at
  probe points (the lean-sdl3 test suite proves this works headless).
- Demo smoke in CI: every demo runs `COMPOSE_MAX_FRAMES=60` under dummy
  drivers on macOS + Linux.
- Env: `COMPOSE_TEST_GROUP=<Name>` runs one group (lean-sdl3 pattern).
- **UI test framework (milestone MT, shipped as `Compose.Test`)** — the
  `androidx.compose.ui.test` analog, built on the semantics `Modifier.Elem`:
  all widgets publish semantics (`SemanticsProps`: testTag, role, text,
  contentDescription, disabled/toggled/selected, editable value, numeric
  range; `Modifier.clickable` merges descendants so a button is findable by
  its label). Lean-first API shape (documented deviation from Kotlin's
  fluent `onNode(...).performClick()` chains): `runComposeTest` boots a real
  window headless with the content composed under a **fake-clock scheduler**
  and runs a `TestM` (ReaderT `UiTest` IO) body; finders are `Matcher`
  literals resolved fresh per call (`find (.text "OK")`, `.tag`, `.role`,
  `.pred`, `and`/`or`/`not`); actions are verbs taking the matcher first
  (`click`/`doubleClick`/`typeText`/`pressKey`/`drag`/`scrollBy`/`moveTo`) —
  every one synthesizes SDL events through the real input router
  (`dispatchEvent` → `InputManager.sdlEvent`, positions mapped
  render→window), never widget callbacks; assertions
  (`assertExists`/`assertMissing`/`assertTextEquals`/`assertEnabled`/
  `assertChecked`/`assertSelected`/`assertFocused`/`assertRangeValue`/
  `assertThat`) print harness-style `ok` lines and **throw with the
  semantics-tree dump** on failure; the clock moves only on
  `advanceTimeBy`/`advanceFrames`/`settle`, with `awaitIdle` draining
  recomposition without advancing time. The 7GUIs demos ship behavior tests
  written in this framework — demo development doubles as the framework's
  own validation. Raw pixel probes remain appropriate only where pixel
  output is itself the property under test.

## Conventions for implementation agents

- Read `AGENTS.md` first (naming, piping style, commit discipline).
- **Lean ergonomics first**: when a public API could mirror Compose or be
  more natural in Lean, pick the Lean shape (see the directive at the top).
- Every public declaration gets a doc comment; cite the Compose analog
  (e.g. "Mirrors `androidx.compose.foundation.layout.Row`") where one exists —
  as a pointer for readers who know Compose, not a fidelity promise.
- Layer discipline is absolute: runtime never imports `Sdl`; ui never imports
  material. `#guard` tests land in the same commit as the definition.
- Build + test before reporting done: `lake build` clean (no warnings,
  no `sorry`), `SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test`.
