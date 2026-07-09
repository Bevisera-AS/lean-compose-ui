# Overview

This project ports Jetpack Compose into Lean 4 on top of
[lean-sdl3](https://github.com/philnguyen/lean-sdl3) (pinned git dependency),
and implements the [7 GUI tasks](https://eugenkiss.github.io/7guis/tasks) as
demos.

**Read `docs/DESIGN.md` before implementing anything** — it is the settled
architecture; deviations require orchestrator sign-off. `docs/ROADMAP.md`
tracks milestones and acceptance criteria.

## Layout

```
Compose/Core/        pure kernel: Color, geometry, Dp/Sp/Density (SDL-free)
Compose/Runtime/     state, composer/slot tree, effects, macro (SDL-free, UI-free)
Compose/Animation/   easing, springs, Animatable, transitions (depends on runtime only)
Compose/Ui/          layout, modifiers, draw, text, input, window/app loop
Compose/Foundation/  Row/Column/Box, scroll, lazy lists, gestures
Compose/Material/    theme + widgets
Demos/               7GUIs demos + gallery
test/ComposeTests/<Area>.lean  runtime test groups, registered in test/ComposeTests.lean
```

Layer discipline is absolute (runtime never imports `Sdl`; ui never imports
material). `Compose/Runtime/SlotVal.lean` is the only module allowed to use
`unsafeCast`.

## Building
- build: `lake build` (needs `brew install sdl3 sdl3_ttf` or equivalent)
- run: `lake exe <target-name>` (demos), `lake exe gallery`
- tests: `SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test`
  (`COMPOSE_TEST_GROUP=<Name>` for one group)
- headless demo smoke: `scripts/smoke-demos.sh` (uses `COMPOSE_MAX_FRAMES`)
- clean: `lake clean`

All SDL video/render/event calls happen on the main thread only — never in
`Task`s. Don't let the last reference to an SDL handle drop inside a `Task`.

## Coding Style
- This project is Compose-INSPIRED, not a 1-1 Kotlin port: keep Compose's
  *semantics* (recomposition, invalidation, animation feel), but shape every
  public API the way a good Lean library would — do-notation, named/default
  args, macros, typeclasses, pipes. Optimize for Lean's ergonomics.
- Prefer dot-abbreviated names to fully qualified names.
- Prefer piping operations using `|>.` or `|>` to nesting parentheses. If a
  piping chain is long, align the steps on multiple lines.
- Every public declaration gets a doc comment; cite the Compose analog where
  one exists (e.g. "Mirrors `androidx.compose.foundation.layout.Row`").
- No warnings, no `sorry` in committed code.

## Testing
- Write plenty of tests, on edge and common cases.
- Prefer `#guard`/`#guard_msgs` commands or `example` with proofs for pure,
  compile-time tests. Such tests should be written as early as possible,
  right below the definition(s) they refer to (i.e. don't defer compile-time
  tests towards the end).
- Runtime behavior (anything touching `IO.Ref`s or SDL) goes in
  `test/ComposeTests/<Area>.lean` (namespace `Tests.<Area>`), registered in
  `test/ComposeTests.lean`; keep every test runnable headless under dummy
  drivers.
- **UI behavior tests use the MT framework** (`Compose.Test`; worked
  examples in `test/ComposeTests/UiTest.lean`). Recipe: give widgets a
  `Modifier.testTag`, boot with `runComposeTest`, drive with matcher-first
  verbs, and wrap each test in `Tests.Harness.scenario` (assertions print
  `ok` lines and throw on failure with a semantics-tree dump):

  ```lean
  open Compose.Test in
  private def counter : IO Unit := do
    let n ← mutableStateOf (0 : Nat)
    runComposeTest
      (content := Tests.restartable 1 do
        Button (n.modify (· + 1)) (content := Text "+1")
        Text s!"count: {← n.get}")
      do
        click (.text "+1")              -- real SDL events, real hit path
        assertExists (.text "count: 1")
        advanceTimeBy 150               -- the clock only moves when told
  -- in the group's `run`: scenario "counter" counter
  ```

  Actions: `click`/`doubleClick`/`typeText`/`pressKey`/`drag`/`scrollBy`/
  `moveTo`. Finders: `find`/`findAll`/`boundsOf` over `.text`/`.tag`/
  `.role`/`.pred` matchers. Assertions: `assertExists`/`Missing`/
  `TextEquals`/`Enabled`/`Checked`/`Selected`/`Focused`/`RangeValue`/`That`.
  Clock: `awaitIdle`/`advanceTimeBy`/`settle`. Use raw pixel probes (the
  `MRig`/`TRig` pattern in the Material/TextField groups) only where pixel
  output is itself the property under test.

## Demos: the main-shim convention

Lean forbids two `_root_.main`s in one import closure, and the test runner
imports every demo's UI for its MT suite — so each demo is split in two:

- a **main-free library module** holding the model + UI
  (e.g. `Demos/Crud.lean`), imported by both the exe and the tests;
- a **thin exe shim** defining only `main` (e.g. `Demos/CrudApp.lean`,
  the `lean_exe` root in `lakefile.lean`).

Every demo *library* module must belong to a `lean_lib` (`Demos`,
`CellsEngine`, `CircleDrawerModel` in `lakefile.lean`): a module reachable
only through an exe root gets no native code built, so the interpreted test
runner cannot load it. To add a demo: lib module (+ `lean_lib` membership),
`<X>Main` shim, `lean_exe`, and register the exe name in `Main.lean`'s
`demos` list — `scripts/smoke-demos.sh` discovers demos via `gallery --list`.

## Version control
- Make small, self-contained commits
- Keep commit messages concise
