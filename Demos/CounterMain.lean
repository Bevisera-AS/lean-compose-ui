import Demos.Counter

/-!
# Counter entry point (`lake exe demo-counter`)

A thin `main` shim over `Demos.Counter`. The demo's screen and logic live in
`Demos/Counter.lean` as a `main`-free library module so the MT test suite
(`test/ComposeTests/Counter.lean`) can import it — Lean forbids two `main`s in
one import closure, so each demo's entry point is split out here.
-/

/-- Entry point. -/
def main : IO UInt32 := do
  let smoke := (← IO.getEnv "COMPOSE_MAX_FRAMES").isSome
  Compose.runApp "compose counter" 320 200 (Demos.Counter.counterApp smoke)
    { clearColor := Compose.ColorScheme.light.background }
