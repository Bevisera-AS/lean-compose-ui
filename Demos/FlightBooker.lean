import Compose

/-!
# Flight Booker demo (`lake exe demo-flight`)

The third 7GUIs task
(<https://eugenkiss.github.io/7guis/tasks#flight-booker>): a combobox choosing
"one-way flight" / "return flight", a start-date field and a return-date field
(the latter enabled only for return flights), and a "Book" button. Dates are
`DD.MM.YYYY`; an ill-formatted date shows error styling and disables Book, and
a return date strictly before the start date also disables Book. Booking opens
a dialog stating the selection. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-flight`.
-/

namespace Demos.FlightBooker
open Compose

/-! ## Pure logic (parse / validate / compare), tested at compile time. -/

/-- A calendar date. -/
structure Date where
  day : Nat
  month : Nat
  year : Nat
deriving BEq, Repr

/-- Days in a (1-based) month of `year`, accounting for leap years; `0` for an
out-of-range month. -/
def daysInMonth (year month : Nat) : Nat :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 then 29 else 28
  | _ => 0

/-- Whether the day/month fall in range for the date's year. -/
def Date.valid (d : Date) : Bool :=
  1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ daysInMonth d.year d.month

/-- A monotone sort key (`YYYYMMDD`), so `≤` on keys is chronological order. -/
def Date.key (d : Date) : Nat := (d.year * 100 + d.month) * 100 + d.day

/-- `a` is on or before `b`. -/
def Date.le (a b : Date) : Bool := a.key ≤ b.key

/-- Value of a validated all-digit string. -/
private def digitsToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Parse a `DD.MM.YYYY` date: exactly two/two/four ASCII digits in valid
ranges; anything else (wrong widths, separators, or out-of-range values) is
`none`. That `none` is what drives the field's error styling and disables Book. -/
def parseDate (s : String) : Option Date :=
  match s.splitOn "." with
  | [d, m, y] =>
    if d.length == 2 && m.length == 2 && y.length == 4
        && d.all Char.isDigit && m.all Char.isDigit && y.all Char.isDigit then
      let dt : Date := { day := digitsToNat d, month := digitsToNat m, year := digitsToNat y }
      if dt.valid then some dt else none
    else none
  | _ => none

/-- The combobox options (also the field's display string). -/
def oneWayLabel : String := "one-way flight"
/-- See `oneWayLabel`. -/
def returnLabel : String := "return flight"

/-- Whether "Book" is enabled: the start date must parse, and for a return
flight the return date must parse and be no earlier than the start. -/
def canBook (isReturn : Bool) (startText returnText : String) : Bool :=
  match parseDate startText with
  | none => false
  | some s =>
    if !isReturn then true
    else match parseDate returnText with
      | none => false
      | some r => s.le r

/-- The confirmation-dialog sentence for the current selection. -/
def bookMessage (isReturn : Bool) (startText returnText : String) : String :=
  if isReturn then
    s!"You have booked a return flight departing {startText} and returning {returnText}."
  else
    s!"You have booked a one-way flight on {startText}."

-- Parsing: the spec's prefilled date, leap years, and rejected forms.
#guard (parseDate "27.03.2014").isSome
#guard (parseDate "29.02.2016").isSome
#guard (parseDate "29.02.2015").isNone
#guard (parseDate "31.04.2014").isNone
#guard (parseDate "00.01.2014").isNone
#guard (parseDate "01.13.2014").isNone
#guard (parseDate "1.3.2014").isNone
#guard (parseDate "27/03/2014").isNone
#guard (parseDate "27.03.14").isNone
#guard (parseDate "aa.bb.cccc").isNone
#guard (parseDate "").isNone
-- Ordering.
#guard Date.le ⟨27, 3, 2014⟩ ⟨28, 3, 2014⟩ = true
#guard Date.le ⟨27, 3, 2014⟩ ⟨27, 3, 2014⟩ = true
#guard Date.le ⟨28, 3, 2014⟩ ⟨27, 3, 2014⟩ = false
#guard Date.le ⟨31, 12, 2013⟩ ⟨01, 01, 2014⟩ = true
-- Booking gate.
#guard canBook false "27.03.2014" "" = true
#guard canBook false "bad" "" = false
#guard canBook true "27.03.2014" "28.03.2014" = true
#guard canBook true "27.03.2014" "27.03.2014" = true
#guard canBook true "27.03.2014" "26.03.2014" = false
#guard canBook true "27.03.2014" "bad" = false
#guard canBook true "bad" "27.03.2014" = false
-- Dialog text.
#guard bookMessage false "27.03.2014" "x" = "You have booked a one-way flight on 27.03.2014."
#guard bookMessage true "27.03.2014" "28.03.2014"
  = "You have booked a return flight departing 27.03.2014 and returning 28.03.2014."

/-! ## The demo. -/

/-- The Flight Booker screen (see the module docstring). The combobox is an
`ExposedDropdownMenuBox`; the two date fields flip `isError` on unparseable
input; Book is enabled per `canBook` and opens an `AlertDialog` with
`bookMessage`. -/
composable def flightBookerUi : Composable Unit := do
  let mode ← remember (mutableStateOf oneWayLabel)
  let expanded ← remember (mutableStateOf false)
  let startText ← remember (mutableStateOf "27.03.2014")
  let returnText ← remember (mutableStateOf "27.03.2014")
  let dialogOpen ← remember (mutableStateOf false)
  let selectedMode ← mode.get
  let open' ← expanded.get
  let s ← startText.get
  let r ← returnText.get
  let dlg ← dialogOpen.get
  let isReturn := selectedMode == returnLabel
  let bookable := canBook isReturn s r
  Column (modifier := Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12) do
    Text "Book Flight" (style := { fontSize := 22 })
    ExposedDropdownMenuBox open' expanded.set fun scope => do
      ExposedDropdownMenuField scope selectedMode (expanded := open')
        (modifier := Modifier.testTag "mode")
      let anchor ← scope.anchor
      DropdownMenu open' (onDismissRequest := expanded.set false) (anchor := anchor)
          (matchAnchorWidth := true) do
        for m in [oneWayLabel, returnLabel] do
          keyed m (DropdownMenuItem m
            (onClick := do mode.set m; expanded.set false))
    TextField s startText.set (label := some "Start date")
      (isError := (parseDate s).isNone) (modifier := Modifier.testTag "start")
    TextField r returnText.set (enabled := isReturn) (label := some "Return date")
      (isError := isReturn && (parseDate r).isNone)
      (modifier := Modifier.testTag "return")
    Button (dialogOpen.set true) (Text "Book") (enabled := bookable)
      (modifier := Modifier.testTag "book")
    if dlg then
      AlertDialog (onDismissRequest := dialogOpen.set false)
        (title := "Flight booked")
        (text := bookMessage isReturn s r)
        (confirmButton := TextButton (dialogOpen.set false) (Text "OK"))

end Demos.FlightBooker
