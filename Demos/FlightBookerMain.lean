import Demos.FlightBooker

/-!
# Flight Booker entry point (`lake exe demo-flight`)

A thin `main` shim over `Demos.FlightBooker` (see `Demos/CounterMain.lean` for
why the entry point is split out from the library module).
-/

/-- Entry point. -/
def main : IO UInt32 := do
  let smoke := (← IO.getEnv "COMPOSE_MAX_FRAMES").isSome
  Compose.runApp "compose flight booker" 360 360
    (Demos.FlightBooker.flightBookerApp smoke)
    { clearColor := Compose.ColorScheme.light.background }
