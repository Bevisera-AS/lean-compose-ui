namespace Compose

/-!
# Semantics properties (`Compose/Ui/Semantics.lean`)

The property record a `Modifier.Elem.semantics` element carries: what a node
*is* (role), what it *says* (text, content description), its interactive
state (disabled/toggled/selected), its editable value, and its numeric range
— everything the MT test framework's finders and assertions consume. Widgets
publish these; nothing at runtime reads them (they are layout- and
draw-inert), so the cost of carrying them is one array slot per chain.

Mirrors the property side of `androidx.compose.ui.semantics` (a
`SemanticsPropertyReceiver` diet shaped as a plain Lean structure with
`Option` fields instead of a keyed map — the property set is closed and
small, so a record is simpler and cheaper). Custom accessibility actions are
deliberately absent: the test framework drives widgets through the real
input pipeline, so there is nothing for an action closure to short-circuit.
-/

namespace Semantics

/-- What kind of control a node is, for role-based finders. Mirrors
`androidx.compose.ui.semantics.Role` (plus the few extra kinds our widget set
needs). -/
inductive Role where
  | button
  | checkbox
  | switch
  | radioButton
  | slider
  | textField
  | progressBar
  | menuItem
  | dialog
  deriving Repr, BEq, Inhabited

/-- Compact rendering for semantics dumps and failure messages. -/
def Role.describe : Role → String
  | .button => "button"
  | .checkbox => "checkbox"
  | .switch => "switch"
  | .radioButton => "radioButton"
  | .slider => "slider"
  | .textField => "textField"
  | .progressBar => "progressBar"
  | .menuItem => "menuItem"
  | .dialog => "dialog"

instance : ToString Role := ⟨Role.describe⟩

/-- A numeric value with its range, as published by sliders and determinate
progress indicators. Mirrors
`androidx.compose.ui.semantics.ProgressBarRangeInfo`. -/
structure Range where
  /-- The current value, in range units. -/
  current : Float32
  /-- Range start. -/
  min : Float32 := 0
  /-- Range end. -/
  max : Float32 := 1
  /-- Discrete steps *between* the endpoints (0 = continuous), matching
  `Slider`'s `steps`. -/
  steps : Nat := 0
  deriving Repr, BEq, Inhabited

end Semantics

/-- The properties of one semantics element. Fields left at their defaults
are "not stated" and fall through to inner elements of the same chain (see
`combine`). Mirrors the `SemanticsConfiguration` produced by
`Modifier.semantics { ... }`. -/
structure SemanticsProps where
  /-- Test-only identity, set via `Modifier.testTag`. Mirrors
  `SemanticsProperties.TestTag`. -/
  testTag : Option String := none
  /-- Static text this node displays (`Text` sets it; a labeled `TextField`
  publishes its label here). Mirrors `SemanticsProperties.Text`. -/
  text : Option String := none
  /-- Accessibility description for non-textual content. Mirrors
  `SemanticsProperties.ContentDescription`. -/
  contentDescription : Option String := none
  /-- Control kind. Mirrors `SemanticsProperties.Role`. -/
  role : Option Semantics.Role := none
  /-- `some true` = explicitly disabled; `some false` = explicitly enabled
  (interactive); `none` = enabledness does not apply. Mirrors
  `SemanticsProperties.Disabled` (with the enabled case made explicit so
  `assertEnabled` can distinguish "enabled control" from "not a control"). -/
  disabled : Option Bool := none
  /-- Checked state of a toggleable (checkbox/switch). Mirrors
  `SemanticsProperties.ToggleableState` (two-state — no indeterminate). -/
  toggled : Option Bool := none
  /-- Selected state (radio button, tabs). Mirrors
  `SemanticsProperties.Selected`. -/
  selected : Option Bool := none
  /-- Current value of an editable text node (`TextField`). Mirrors
  `SemanticsProperties.EditableText`. -/
  editableText : Option String := none
  /-- Numeric value + range (slider, determinate progress). Mirrors
  `SemanticsProperties.ProgressBarRangeInfo`. -/
  range : Option Semantics.Range := none
  /-- Merge descendant semantics into this node in the merged tree (set by
  `Modifier.clickable`, so a `Button`'s label text is findable *on the
  button*). Mirrors `Modifier.semantics(mergeDescendants = true)`. -/
  mergeDescendants : Bool := false
  deriving Repr, BEq, Inhabited

namespace SemanticsProps

/-- Combine two elements of the same chain, the `outer` one winning every
field it states (Compose's outer-modifier-wins semantics ordering);
`mergeDescendants` is sticky. -/
def combine (outer inner : SemanticsProps) : SemanticsProps where
  testTag := outer.testTag <|> inner.testTag
  text := outer.text <|> inner.text
  contentDescription := outer.contentDescription <|> inner.contentDescription
  role := outer.role <|> inner.role
  disabled := outer.disabled <|> inner.disabled
  toggled := outer.toggled <|> inner.toggled
  selected := outer.selected <|> inner.selected
  editableText := outer.editableText <|> inner.editableText
  range := outer.range <|> inner.range
  mergeDescendants := outer.mergeDescendants || inner.mergeDescendants

#guard (combine { testTag := some "a" } { testTag := some "b", role := some .button })
        == { testTag := some "a", role := some .button }
#guard (combine { disabled := some false } { disabled := some true })
        == { disabled := some false }
#guard (combine {} { mergeDescendants := true }).mergeDescendants
#guard (combine { toggled := some false } {}).toggled == some false
#guard combine {} {} == ({} : SemanticsProps)

/-- One-line rendering for semantics dumps: only the stated fields, in a
stable order, e.g. `role=button tag="inc" text="+1" disabled merge`. -/
def describe (p : SemanticsProps) : String := Id.run do
  let mut parts : Array String := #[]
  if let some r := p.role then parts := parts.push s!"role={r}"
  if let some t := p.testTag then parts := parts.push s!"tag=\"{t}\""
  if let some t := p.text then parts := parts.push s!"text=\"{t}\""
  if let some d := p.contentDescription then parts := parts.push s!"desc=\"{d}\""
  if let some e := p.editableText then parts := parts.push s!"value=\"{e}\""
  match p.disabled with
  | some true => parts := parts.push "disabled"
  | some false => parts := parts.push "enabled"
  | none => pure ()
  if let some t := p.toggled then
    parts := parts.push (if t then "toggled=on" else "toggled=off")
  if let some s := p.selected then
    parts := parts.push (if s then "selected" else "unselected")
  if let some r := p.range then
    parts := parts.push s!"range={r.current}∈[{r.min},{r.max}]"
  if p.mergeDescendants then parts := parts.push "merge"
  return " ".intercalate parts.toList

#guard describe { role := some .button, testTag := some "inc", mergeDescendants := true }
        == "role=button tag=\"inc\" merge"
#guard describe { text := some "hi", disabled := some true } == "text=\"hi\" disabled"
#guard describe {} == ""

end SemanticsProps

end Compose
