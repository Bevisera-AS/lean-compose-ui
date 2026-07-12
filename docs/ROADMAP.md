# Roadmap

Milestones toward `docs/DESIGN.md`. Each lands as a series of small commits
with its tests; a milestone is done when `lake build` is clean and
`SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test` passes.

| # | Milestone | Contents | Acceptance |
|---|---|---|---|
| M0 | Scaffolding | dep pin, `Compose/Core/*` kernel, CI, docs | ✅ builds; kernel `#guard`s pass |
| M1 | Runtime core | `SlotVal`, `State`, `Applier`, `Composer` (groups, positional memoization, insert/remove/move), `Recomposer`, `remember`/`keyed`, effects, `CompositionLocal` | TestApplier suites: recomposition reuses nodes, conditional content inserts/removes at right indices, `keyed` reorder moves nodes, effect launch/dispose ordering, state-write → exactly the reading scopes re-run |
| M2 | `composable` macro | restartable defs, skippability via `SkipEq`, auto group keys for `if`/`match`/`for`, `composable fun` | macro-authored counter/conditional/loop compositions recompose correctly; skipped when args equal; explicit-combinator API still works |
| M3 | Draw stack | `Tessellate` (pure, feathered-AA meshes), `Brush`, `DrawScope` (transform/clip stacks), SDL renderer backend | `#guard` mesh tests; headless pixel assertions: fills, rounded corners, strokes, clip nesting, gradients |
| M4 | Layout | `Constraints`, `Modifier` + elems, `LayoutNode`, measure/place, dirty tracking, `Row`/`Column`/`Box`/`Spacer` with arrangement/alignment/weight | layout unit suites: padding/size/fill/offset, weights, alignments, nested trees; state-read in measure invalidates exactly that node |
| M5 | App shell | `Scheduler`/`UiTask`, frame clock, `WindowContext`, event loop (wait-with-deadline, dirty-driven), density/HiDPI, `runApp`, `COMPOSE_MAX_FRAMES` | a no-macro counter demo runs windowed; headless smoke passes; idle loop blocks (no busy spin) |
| M6 | Input | pointer translate/hit-test/dispatch, gesture detectors (tap/double/long/drag/hover/wheel), focus manager + Tab traversal, key routing, cursor shapes | synthetic-event suites: hit paths respect z-order+clip, consumption, hover enter/exit diffing, focus order, click activation via keyboard |
| M7 | Text | `FontStore`, bundled font + fallbacks, `TextLayout` over renderer text engine, `Material.Text` composable | text measures/wraps/draws; pixel test shows glyphs; layout caching (no re-shape when unchanged) |
| M8 | Animation | easing, tween/spring/keyframes/repeat specs, `VectorConverter`, `Animatable` (velocity, interruption), `animate*AsState`, `Transition`, `InfiniteTransition`, `AnimatedVisibility` | math `#guard`s (spring closed forms, bézier); runtime: interruption preserves velocity, target-change relaunch, visibility keeps content until exit done |
| M9 | Material core | theme (color schemes light/dark, typography, shapes), state layers + bounded ripple, `Surface` `Button` `Checkbox` `RadioButton` `Switch` `Slider` `ProgressIndicator`s `Divider` | widget gallery demo; interaction states animate; keyboard operable; pixel probes on states |
| M10 | Scroll & overlays | scroll state/modifier + wheel, `Scrollbar`, LazyColumn-lite, `Popup`/`DropdownMenu`/`AlertDialog` overlay system | scroll clamps/virtualizes correctly; popup positioning, dismiss semantics, dialog scrim blocks input below |
| M11 | TextField | pure `EditModel` (+exhaustive `#guard`s), caret/selection rendering, mouse+keyboard selection, clipboard, IME composition, auto-scroll, outlined Material look | scripted end-to-end editing tests headless; IME events honored; UTF-8 safe |
| MT | UI test framework | `Compose.Test`, mirroring `androidx.compose.ui.test` with a Lean-first shape: semantics tree (`Modifier.semantics`/`testTag` — role, text, contentDescription, disabled/toggled/selected, editable value, ranges; merged + unmerged views) populated by ALL widgets (Text, Button, Checkbox, RadioButton, Switch, Slider, Progress, TextField, DropdownMenu, Dialog); `runComposeTest` (headless bootstrap + fake-clock scheduler); `Matcher` finders (`find (.text …)`, `.tag`, `.role`, `.pred`, combinators); actions (`click/doubleClick/typeText/pressKey/drag/scrollBy/moveTo` — synthesized through the REAL input router, not direct callbacks); assertions (`assertExists/Missing/TextEquals/Enabled/Checked/Selected/Focused/RangeValue/That`, failures dump the semantics tree); `awaitIdle`/`advanceTimeBy`/`settle` clock control | ✅ `UiTest` self-test group (10 scenarios: finders/dumps, real-router clicks/keys/text/drag/wheel, overlays, frozen-clock animation); 5 Material/TextField suites rewritten in it; AGENTS.md how-to for demo authors |
| M12 | Demos 1–6 | Counter, TempConverter, FlightBooker, Timer, CRUD, CircleDrawer (+ gallery launcher `--list`) | each matches the 7GUIs spec; headless smoke; undo/redo correct in CircleDrawer; **each demo ships a behavior test suite written with the MT framework** (which dogfoods MT itself) |
| M13 | Cells | 2-axis virtualized grid w/ sticky headers, selection/editing, formula parser+evaluator+dependency graph (pure), reactive recalc, cycle detection | formula `#guard` suite; scrolling stays 60fps on 99×26; change propagation matches spec; **grid/editing behavior tests written with MT** |
| M14 | Polish | **phase 1** ✅ widget polish (ripple, animated menu exit, modal focus scoping, TextField keys) + framework promotions (LazyGrid, shared scrollbar core, `FocusRequester`); **phase 2** ✅ Foundation/MT ergonomics pass (dropped `Row`/`Column`/`Box` receiver scopes; MT `replaceText`/`requestFocus`) + perf audit (DESIGN.md "Performance"); **phase 3** ✅ README + `docs/screenshots/` (via `COMPOSE_SCREENSHOT`) + gallery launcher UI + tessellation cache (DESIGN.md "Performance") | ✅ `lake build` clean; `lake exe test` green; README quick start verified; idle blocks (no busy-spin) |
| M15 | Desktop components | multi-window `application`/`Window`/`DialogWindow`, system `Tray`, in-window `MenuBar`, `ContextMenuArea`, `TooltipArea` (scrollbars landed in M14) | ✅ per-component MT suites + `demo-desktop` showcase and smoke |
| MG | GPU renderer | display-list IR + `RenderBackend` seam; SDL_GPU backend: instanced SDF quads, analytic Gaussian shadows, offscreen layers (group opacity), exact rounded clipping, glyph-atlas text; `Modifier.shadow` + `Surface` elevation | ✅ IR goldens + SDL-fallback pixel tests headless; on a real driver `scripts/smoke-gpu.sh` runs `gpu-probe` pixel asserts, the `gpu-parity` GPU↔SDL diff, and every demo |

Status: complete — all milestones (M0–M15, MT, MG) have landed.

Parallelization: M1 ∥ M3 · then M2 ∥ M4 · M5 · then M6 ∥ M7 ∥ M8 ·
M9 · then M10 ∥ M11 · MT · then M12 ∥ M13 · M14.

## Renderer capability expansion

Post-MG waves closing the gap to Skia/Impeller-class renderers (plan approved
2026-07-12). Same acceptance per wave: zero-warning build, headless suite,
`smoke-demos.sh`, `smoke-gpu.sh`.

| # | Wave | Contents | Status |
|---|---|---|---|
| M-e1 | Path fill | `Path` verb model + `Path.build` (arcs lower to cubics), adaptive flatten, winding oracle; band-sweep fill tessellator + 1-px feather (`PathFill.lean`), oracle `#guard` corpus + fuzz; `ShapeSpec.pathFill` through both backends; `drawPath` (provisional stroke); `PathDraw` group, gpu-probe step ⑨, gpu-parity "paths" scene | ✅ |
| M-e2 | Stroker | joins/caps/miter-limit/dashing (`PathStroke.lean`), stroke-to-fill through the M-e1 sweep; `clipPath` (exact dual-winding path fills, `pathFillClipped`); SDL backend rounds mesh vertices to whole pixels (software-rasterizer truncation fix) | ✅ |
| M-f | Images | `ImageBitmap` (BMP+PNG via SDL 3.4 `loadSurface`; `ofPixels` generator; rgba32 straight alpha, id-keyed), `Prim.image`/`drawImage`, never-evict texture caches on both backends (GPU: premultiplied upload, layer pipeline + linear sampler), `Image` composable + `ContentScale` (`Foundation/Image.lean`) | ✅ |
| M-g | Transforms | `Affine`, `graphicsLayer` (rotate/scale at layer boundaries), real SDL offscreen layers, `snapComposite` text heuristic | — |
| M-h | Gradients | radial/sweep brushes, GPU quad `gradKind` packing, IGN dithering | — |
| M-i | Blur | `LayerEffect.blur`, separable Gaussian layer passes (GPU-only) | — |
| M-j | Subpixel text | shared run-origin snap on both backends, fractional-origin parity scene | — |
