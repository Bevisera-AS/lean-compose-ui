import Demos.TempConverter

/-!
# Temperature Converter entry point (`lake exe demo-tempconv`)

A thin `main` shim over `Demos.TempConverter` (see `Demos/CounterMain.lean` for
why the entry point is split out from the library module).
-/

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose temperature converter" 340 300
    Demos.TempConverter.tempConverterUi
    { clearColor := Compose.ColorScheme.light.surface }
