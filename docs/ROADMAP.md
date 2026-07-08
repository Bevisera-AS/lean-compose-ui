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
| M12 | Demos 1–6 | Counter, TempConverter, FlightBooker, Timer, CRUD, CircleDrawer (+ gallery launcher `--list`) | each matches the 7GUIs spec; headless smoke; undo/redo correct in CircleDrawer |
| M13 | Cells | 2-axis virtualized grid w/ sticky headers, selection/editing, formula parser+evaluator+dependency graph (pure), reactive recalc, cycle detection | formula `#guard` suite; scrolling stays 60fps on 99×26; change propagation matches spec |
| M14 | Polish | README with screenshots, perf pass (frame-time budget, allocation audit), debug overlay, API doc sweep | idle 0% CPU; interaction 60fps; README quick start verified from scratch |

Parallelization: M1 ∥ M3 · then M2 ∥ M4 · M5 · then M6 ∥ M7 ∥ M8 ·
M9 · then M10 ∥ M11 · then M12 ∥ M13 · M14.
