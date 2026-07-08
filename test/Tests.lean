import Compose

/-- Runtime test harness. Groups register here as milestones land; pure logic
is tested at compile time with `#guard` next to the definitions instead.
Run headless: `SDL_VIDEO_DRIVER=dummy lake exe test`. -/
def main : IO UInt32 := do
  IO.println "compose-ui tests: ok (no runtime groups yet)"
  return 0
