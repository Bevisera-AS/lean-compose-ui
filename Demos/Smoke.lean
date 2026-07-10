import Compose

/-!
# Smoke demo (`lake exe demo-smoke`)

The M5 shell exerciser: a `Column` of three `Box`es whose background colors
cycle every 500 ms through a `LaunchedEffect` timer loop, plus a fourth box
whose width oscillates every frame via `UiTask.awaitFrame` (a manual lerp —
the real animation API is M8). Together this proves recomposition,
remeasure, redraw, the frame clock, timers, and quit handling. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-smoke`.
-/

namespace Demos.Smoke
open Compose

/-- The cycling background palette. -/
def palette : Array Color := #[.red, .green, .blue, .yellow, .cyan, .magenta]

/-- Advance the palette phase every 500 ms, forever. -/
partial def cyclePalette (phase : MutableState Nat) : UiTask Unit := do
  UiTask.delay 500
  phase.modify (· + 1)
  cyclePalette phase

/-- Oscillate `width` between 40 and 200 dp on the frame clock: a manual
triangle-wave lerp with a 2 s period (M8 replaces this with `Animatable`). -/
partial def animateWidth (width : MutableState Dp) : UiTask Unit := do
  let ns ← UiTask.awaitFrame
  let period := 2_000_000_000
  let t := (ns % period).toFloat32 / period.toFloat32          -- [0, 1)
  let tri := if t < 0.5 then 2 * t else 2 * (1 - t)            -- triangle wave
  width.set ⟨40 + 160 * tri⟩
  animateWidth width

/-- A fixed-size box filled with the palette color at `phase + offset`. -/
composable def paletteBox (phase : Nat) (offset : Nat) : Composable Unit := do
  Box (modifier := Modifier.size 120 40 |>.background palette[(phase + offset) % palette.size]!)

/-- The demo UI (see the module docstring). -/
composable def smokeUi : Composable Unit := do
  let phase ← remember (mutableStateOf (0 : Nat))
  let width ← remember (mutableStateOf (40 : Dp))
  LaunchedEffect 0 (cyclePalette phase)
  LaunchedEffect 1 (animateWidth width)
  Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12) do
    let p ← phase.get
    for i in [0:3] do
      paletteBox p i
    let w ← width.get
    Box (modifier := Modifier.size w 24 |>.background .darkGray)

end Demos.Smoke

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose smoke" 320 280 Demos.Smoke.smokeUi
    { clearColor := Compose.Color.lightGray }
