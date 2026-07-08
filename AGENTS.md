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
test/Tests/<Area>.lean  runtime test groups, registered in test/Tests.lean
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
  `test/Tests/<Area>.lean`; keep every test runnable headless under dummy
  drivers.

## Version control
- Make small, self-contained commits
- Keep commit messages concise
