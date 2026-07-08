# compose-ui

A [Jetpack Compose](https://github.com/jetbrains/compose-multiplatform)-style
declarative UI framework for [Lean 4](https://lean-lang.org), rendered with
SDL3 via [lean-sdl3](https://github.com/philnguyen/lean-sdl3) — plus the
[7GUIs tasks](https://eugenkiss.github.io/7guis/tasks) as demos.

**Status: under construction.** See `docs/DESIGN.md` for the architecture and
`docs/ROADMAP.md` for progress.

## Quick start

```sh
brew install sdl3 sdl3_ttf   # macOS; Linux: build SDL3/SDL3_ttf from source
lake build
lake exe gallery             # demo launcher (as demos land)
SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake exe test
```

## License

Apache-2.0. Bundled Roboto fonts are OFL-1.1 (`assets/fonts/`).
