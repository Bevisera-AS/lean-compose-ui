import Compose.Test.Finders

namespace Compose.Test

/-!
# Assertions (`Compose/Test/Assertions.lean`)

Checks over found nodes, in the repo's harness convention: a passing
assertion prints one `ok <name>` line (so the suite's check counter sees
it); a failing one **throws** an `IO` error carrying the reason *and the
full semantics dump* — `Tests.Harness.group` (or the test file's scenario
wrapper) turns that into a counted failure. Assertions that need a unique
node inherit `find`'s found-0/found-N failures too.

Mirrors `assertExists` / `assertDoesNotExist` / `assertTextEquals` /
`assertIsEnabled` / `assertIsOn` / `assertIsSelected` / `assertIsFocused` /
`assertRangeInfoEquals` — as `TestM` verbs taking the `Matcher` first.
-/

/-- Record a passing check (one `ok` line, harness-countable). -/
private def pass (name : String) : TestM Unit :=
  IO.println s!"ok {name}"

/-- Pass/fail one named condition on the unique node matching `m`; the
failure message shows the node and the tree. The generic building block —
`assertThat (.tag "x") "is wide" (fun n => n.bounds.width > 100)`. -/
def assertThat (m : Matcher) (label : String) (cond : SemanticsNode → Bool) :
    TestM Unit := do
  let n ← find m
  if cond n then
    pass s!"assert {m.description} {label}"
  else
    failWithDump s!"assert {m.description} {label}: failed on {n.describe}"

/-- At least one node matches. Mirrors `assertExists`. -/
def assertExists (m : Matcher) : TestM Unit := do
  if (← findAll m).isEmpty then
    failWithDump s!"assertExists {m.description}: no matching node"
  pass s!"assertExists {m.description}"

/-- No node matches. Mirrors `assertDoesNotExist`. -/
def assertMissing (m : Matcher) : TestM Unit := do
  let hits ← findAll m
  unless hits.isEmpty do
    failWithDump s!"assertMissing {m.description}: found {hits.size}"
  pass s!"assertMissing {m.description}"

/-- Exactly `n` nodes match. Mirrors `assertCountEquals`. -/
def assertCountEquals (m : Matcher) (n : Nat) (unmerged : Bool := false) :
    TestM Unit := do
  let hits ← findAll m unmerged
  unless hits.size == n do
    failWithDump s!"assertCountEquals {m.description}: expected {n}, found {hits.size}"
  pass s!"assertCountEquals {m.description} = {n}"

/-- The node's editable value — or, for non-editable nodes, its sole text —
equals `expected` (nodes with several merged texts need
`assertTextContains`). Mirrors `assertTextEquals`. -/
def assertTextEquals (m : Matcher) (expected : String) : TestM Unit := do
  let n ← find m
  let ok := match n.props.editableText with
    | some v => v == expected
    | none => n.texts == #[expected]
  if ok then
    pass s!"assertTextEquals {m.description} = \"{expected}\""
  else
    failWithDump s!"assertTextEquals {m.description}: expected \"{expected}\", \
                    got {n.describe}"

/-- Some text (or the editable value) of the node contains `needle`. -/
def assertTextContains (m : Matcher) (needle : String) : TestM Unit :=
  assertThat m s!"has text containing \"{needle}\"" (Matcher.textContains needle).test

/-- The node is an *enabled* control (a widget that stated
`disabled := some false`). Mirrors `assertIsEnabled`. -/
def assertEnabled (m : Matcher) : TestM Unit :=
  assertThat m "is enabled" (·.props.disabled == some false)

/-- The node is a disabled control. Mirrors `assertIsNotEnabled`. -/
def assertDisabled (m : Matcher) : TestM Unit :=
  assertThat m "is disabled" (·.props.disabled == some true)

/-- A toggleable (checkbox/switch) is on. Mirrors `assertIsOn`. -/
def assertChecked (m : Matcher) : TestM Unit :=
  assertThat m "is checked" (·.props.toggled == some true)

/-- A toggleable is off. Mirrors `assertIsOff`. -/
def assertUnchecked (m : Matcher) : TestM Unit :=
  assertThat m "is unchecked" (·.props.toggled == some false)

/-- The node's selected state (radio buttons) equals `expected`. Mirrors
`assertIsSelected`/`assertIsNotSelected`. -/
def assertSelected (m : Matcher) (expected : Bool := true) : TestM Unit :=
  assertThat m s!"is {if expected then "selected" else "unselected"}"
    (·.props.selected == some expected)

/-- The node's range value (slider/progress) is within `tol` of `expected`.
Mirrors `assertRangeInfoEquals`. -/
def assertRangeValue (m : Matcher) (expected : Float32) (tol : Float32 := 1e-4) :
    TestM Unit :=
  assertThat m s!"has range value ≈ {expected}" fun n =>
    match n.props.range with
    | some r => (r.current - expected).abs ≤ tol
    | none => false

/-- The node holds keyboard focus. Mirrors `assertIsFocused`. -/
def assertFocused (m : Matcher) : TestM Unit := do
  let n ← find m
  let ok ← match ← focusedNode with
    | some f => do pure ((← f.nodeId) == (← n.layout.nodeId))
    | none => pure false
  if ok then
    pass s!"assertFocused {m.description}"
  else
    failWithDump s!"assertFocused {m.description}: focus is elsewhere"

/-- The node does not hold keyboard focus. Mirrors `assertIsNotFocused`. -/
def assertNotFocused (m : Matcher) : TestM Unit := do
  let n ← find m
  let focused ← match ← focusedNode with
    | some f => do pure ((← f.nodeId) == (← n.layout.nodeId))
    | none => pure false
  if focused then
    failWithDump s!"assertNotFocused {m.description}: node is focused"
  else
    pass s!"assertNotFocused {m.description}"

end Compose.Test
