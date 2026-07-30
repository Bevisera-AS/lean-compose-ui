import Compose
import ComposeTests.Harness
import Demos.TempConverter

/-!
# Temperature Converter demo tests (`test/ComposeTests/TempConverter.lean`)

MT behavior tests for `Demos/TempConverter.lean`: bidirectional conversion
(editing one field updates the other) and the spec's inertness rule (typing
something unparseable leaves the sibling field untouched). Drives the imported
demo composable through the real IME/text path.
-/

namespace Tests.TempConverter
open Compose Compose.Test Tests.Harness

/-- Typing a Celsius value fills Fahrenheit (`100 °C → 212 °F`). -/
private def celsiusToFahrenheit : IO Unit := runComposeTest
  Demos.TempConverter.tempConverterUi (theme := none)
  (width := 360) (height := 320)
  do
    assertTextEquals (.tag "celsius") ""
    assertTextEquals (.tag "fahrenheit") ""
    typeText (.tag "celsius") "100"
    assertTextEquals (.tag "celsius") "100"
    assertTextEquals (.tag "fahrenheit") "212"

/-- Typing a Fahrenheit value fills Celsius (`212 °F → 100 °C`). -/
private def fahrenheitToCelsius : IO Unit := runComposeTest
  Demos.TempConverter.tempConverterUi (theme := none)
  (width := 360) (height := 320)
  do
    typeText (.tag "fahrenheit") "212"
    assertTextEquals (.tag "fahrenheit") "212"
    assertTextEquals (.tag "celsius") "100"

/-- Unparseable input is inert: the sibling field keeps its last good value. -/
private def invalidIsInert : IO Unit := runComposeTest
  Demos.TempConverter.tempConverterUi (theme := none)
  (width := 360) (height := 320)
  do
    typeText (.tag "celsius") "50"
    assertTextEquals (.tag "fahrenheit") "122"
    -- A non-numeric edit of Fahrenheit must not disturb Celsius.
    typeText (.tag "fahrenheit") "z"
    assertTextEquals (.tag "celsius") "50"

/-- The TempConverter group. -/
def run : IO Unit := do
  scenario "celsiusToFahrenheit" celsiusToFahrenheit
  scenario "fahrenheitToCelsius" fahrenheitToCelsius
  scenario "invalidIsInert" invalidIsInert

end Tests.TempConverter
