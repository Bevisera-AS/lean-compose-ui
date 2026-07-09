import Compose

/-!
# Temperature Converter demo (`lake exe demo-tempconv`)

The second 7GUIs task
(<https://eugenkiss.github.io/7guis/tasks#temperature-converter>): two text
fields, Celsius and Fahrenheit, kept in sync. Editing one recomputes the other
**only** when the edited text parses as a number (`C = (F−32)·5/9`,
`F = C·9/5+32`); otherwise the other field is left untouched. Values are shown
rounded to at most two decimals. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-tempconv`.
-/

namespace Demos.TempConverter
open Compose

/-! ## Pure logic (parse / convert / format), tested at compile time. -/

/-- `some n` iff `s` is a nonempty run of ASCII digits. -/
private def digitsToNat? (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else some (s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)

/-- Negate `x` when `neg`. -/
private def applySign (neg : Bool) (x : Float) : Float := if neg then -x else x

/-- Parse a decimal number: optional leading `+`/`-`, then digits with an
optional single `.` and fractional digits (either side may be empty, but not
both). Surrounding whitespace is ignored. Anything else is `none` — which is
exactly what keeps the sibling field inert on bad input. -/
def parseNumber (s0 : String) : Option Float :=
  let cs := s0.trimAscii.toString.toList
  let (neg, rest) := match cs with
    | '-' :: t => (true, t)
    | '+' :: t => (false, t)
    | _ => (false, cs)
  match (String.ofList rest).splitOn "." with
  | [ip] => (digitsToNat? ip).map (fun n => applySign neg n.toFloat)
  | [ip, fp] =>
    if ip.isEmpty && fp.isEmpty then none
    else
      let ipN := if ip.isEmpty then some 0 else digitsToNat? ip
      let fpN := if fp.isEmpty then some 0 else digitsToNat? fp
      match ipN, fpN with
      | some iv, some fv =>
        some (applySign neg (iv.toFloat + fv.toFloat / (10 ^ fp.length).toFloat))
      | _, _ => none
  | _ => none

/-- Celsius → Fahrenheit. -/
def cToF (c : Float) : Float := c * 9.0 / 5.0 + 32.0

/-- Fahrenheit → Celsius. -/
def fToC (f : Float) : Float := (f - 32.0) * 5.0 / 9.0

/-- Round to the nearest hundredth, as a signed integer count of hundredths. -/
private def roundHundredths (x : Float) : Int :=
  if x < 0 then -(Int.ofNat (((-x) * 100.0 + 0.5).toUInt64.toNat))
  else Int.ofNat ((x * 100.0 + 0.5).toUInt64.toNat)

/-- Render a signed hundredths count, trimming trailing zeros (`120` →
`"1.2"`, `100` → `"1"`, `5` → `"0.05"`). -/
private def fmtHundredths (n : Int) : String :=
  let a := n.natAbs
  let whole := a / 100
  let frac := a % 100
  let body :=
    if frac == 0 then toString whole
    else if frac % 10 == 0 then s!"{whole}.{frac / 10}"
    else if frac < 10 then s!"{whole}.0{frac}"
    else s!"{whole}.{frac}"
  if n < 0 then "-" ++ body else body

/-- Display a temperature rounded to at most two decimals (no `3.0000001`). -/
def fmtTemp (x : Float) : String := fmtHundredths (roundHundredths x)

-- Conversions + rounding.
#guard fmtTemp (cToF 100) = "212"
#guard fmtTemp (cToF 0) = "32"
#guard fmtTemp (cToF 37) = "98.6"
#guard fmtTemp (cToF (-40)) = "-40"
#guard fmtTemp (fToC 32) = "0"
#guard fmtTemp (fToC 212) = "100"
#guard fmtTemp (fToC (-40)) = "-40"
#guard fmtTemp 0.05 = "0.05"
-- Parsing: valid forms round-trip through `fmtTemp`.
#guard (parseNumber "12").map fmtTemp = some "12"
#guard (parseNumber "  12  ").map fmtTemp = some "12"
#guard (parseNumber "12.").map fmtTemp = some "12"
#guard (parseNumber "3.5").map fmtTemp = some "3.5"
#guard (parseNumber "-3.5").map fmtTemp = some "-3.5"
#guard (parseNumber ".5").map fmtTemp = some "0.5"
#guard (parseNumber "10.25").map fmtTemp = some "10.25"
-- Parsing: rejected forms are inert (`none`).
#guard (parseNumber "").isNone
#guard (parseNumber "abc").isNone
#guard (parseNumber "1.2.3").isNone
#guard (parseNumber "-").isNone
#guard (parseNumber "3x").isNone

/-! ## The demo. -/

/-- The Temperature Converter screen (see the module docstring). Each field is
a `TextFieldS`; on edit it stores the raw text and, only if it parses, writes
the converted value to the sibling. Unparseable input flips `isError` (error
outline/label) and leaves the sibling untouched. -/
composable def tempConverterUi : Composable Unit := do
  let celsius ← remember (mutableStateOf "")
  let fahrenheit ← remember (mutableStateOf "")
  let c ← celsius.get
  let f ← fahrenheit.get
  MaterialTheme (content :=
    Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12)
      (content := do
        Text "Temperature Converter" (style := { fontSize := 22 })
        TextFieldS c
          (fun t => do
            celsius.set t
            match parseNumber t with
            | some v => fahrenheit.set (fmtTemp (cToF v))
            | none => pure ())
          (label := some "Celsius")
          (isError := !c.trimAscii.toString.isEmpty && (parseNumber c).isNone)
          (modifier := Modifier.testTag "celsius")
        Text "="
        TextFieldS f
          (fun t => do
            fahrenheit.set t
            match parseNumber t with
            | some v => celsius.set (fmtTemp (fToC v))
            | none => pure ())
          (label := some "Fahrenheit")
          (isError := !f.trimAscii.toString.isEmpty && (parseNumber f).isNone)
          (modifier := Modifier.testTag "fahrenheit")))

end Demos.TempConverter
