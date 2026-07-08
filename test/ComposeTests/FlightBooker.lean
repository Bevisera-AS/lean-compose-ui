import Compose
import ComposeTests.Harness
import Demos.FlightBooker

/-!
# Flight Booker demo tests (`test/ComposeTests/FlightBooker.lean`)

MT behavior tests for `Demos/FlightBooker.lean`: the combobox switches flight
mode, which enables/disables the return-date field; validation (bad date, or a
return date before the start) disables Book; and Book opens a dialog stating
the selection. Drives the imported demo composable through the real combobox,
text, and overlay paths.
-/

namespace Tests.FlightBooker
open Compose Compose.Test Tests.Harness

/-- Mode switching gates the return field, and validation gates Book. -/
private def validationAndCombobox : IO Unit := runComposeTest
  (content := Demos.FlightBooker.flightBookerUi) (theme := false)
  (width := 360) (height := 400)
  do
    -- One-way by default: return field disabled; the prefilled date is valid,
    -- so Book is enabled.
    assertExists (.tag "mode")
    assertDisabled (.tag "return")
    assertEnabled (.tag "start")
    assertEnabled (.tag "book")
    -- Switch to "return flight" through the combobox.
    click (.tag "mode")
    settle
    click (.text "return flight")
    assertEnabled (.tag "return")
    -- Start == return (both prefilled 27.03.2014): equal counts as valid.
    assertEnabled (.tag "book")
    -- Corrupting the return date makes it unparseable → Book disabled.
    typeText (.tag "return") "9"
    assertDisabled (.tag "book")

/-- Clicking Book opens an AlertDialog stating the (one-way) selection. -/
private def bookingDialog : IO Unit := runComposeTest
  (content := Demos.FlightBooker.flightBookerUi) (theme := false)
  (width := 360) (height := 400)
  do
    assertMissing (.role .dialog)
    click (.tag "book")
    assertExists (.role .dialog)
    assertExists (.text "You have booked a one-way flight on 27.03.2014.")
    click (.text "OK")
    assertMissing (.role .dialog)

/-- The FlightBooker group. -/
def run : IO Unit := do
  scenario "validationAndCombobox" validationAndCombobox
  scenario "bookingDialog" bookingDialog

end Tests.FlightBooker
