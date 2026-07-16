module

public import Compose.Test.Harness
public meta import Compose.Test.Harness

public section

namespace Compose.Test

/-!
# Finders (`Compose/Test/Finders.lean`)

`Matcher`s select semantics nodes; `find`/`findAll` resolve them against the
*current* tree (after `awaitIdle`), so a matcher can be reused across
recompositions — the Lean spelling of `onNodeWithText`/`onNodeWithTag`/
`onAllNodes(matcher)`. Since action/assertion parameters are `Matcher`-typed,
anonymous-constructor dot notation reads like a DSL:

```lean
click (.text "Increment")
assertChecked (.tag "opt-in")
find (.role .slider) -- the node itself, for custom checks
```

Failed resolutions throw with the full semantics dump attached.
-/

/-- A semantics-node predicate with a human-readable description (used in
failure messages and printed check names). Mirrors `SemanticsMatcher`. -/
structure Matcher where
  /-- E.g. `text "OK"` — reads well after `assertExists`. -/
  description : String
  /-- Whether a node matches. -/
  test : SemanticsNode → Bool

namespace Matcher

/-- Whether `needle` occurs in `hay`. -/
private def substr (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

#guard substr "hello world" "lo w"
#guard substr "hello" ""
#guard !substr "hello" "z"

/-- Node whose (merged) texts or editable value equal `s`. Mirrors
`hasText(s)` / `onNodeWithText`. -/
def text (s : String) : Matcher :=
  ⟨s!"text \"{s}\"", fun n => n.texts.contains s || n.props.editableText == some s⟩

/-- Node whose texts or editable value *contain* `s`. Mirrors
`hasText(s, substring = true)`. -/
def textContains (s : String) : Matcher :=
  ⟨s!"text containing \"{s}\"", fun n =>
    n.texts.any (substr · s) || (n.props.editableText.map (substr · s)).getD false⟩

/-- Node tagged `Modifier.testTag s`. Mirrors `hasTestTag` /
`onNodeWithTag`. -/
def tag (s : String) : Matcher :=
  ⟨s!"tag \"{s}\"", fun n => n.props.testTag == some s⟩

/-- Node with the given role. Mirrors `SemanticsMatcher.expectValue(Role, r)`. -/
def role (r : Semantics.Role) : Matcher :=
  ⟨s!"role {r}", fun n => n.props.role == some r⟩

/-- Custom predicate with a description. -/
def pred (description : String) (test : SemanticsNode → Bool) : Matcher :=
  ⟨description, test⟩

/-- Both match. Mirrors `SemanticsMatcher.and`. -/
def and (a b : Matcher) : Matcher :=
  ⟨s!"{a.description} and {b.description}", fun n => a.test n && b.test n⟩

/-- Either matches. Mirrors `SemanticsMatcher.or`. -/
def or (a b : Matcher) : Matcher :=
  ⟨s!"{a.description} or {b.description}", fun n => a.test n || b.test n⟩

/-- Negation. -/
def not (a : Matcher) : Matcher :=
  ⟨s!"not ({a.description})", fun n => !a.test n⟩

/-- A detached node for the matcher `#guard`s below. -/
private def probe (props : SemanticsProps := {}) (texts : Array String := #[]) :
    SemanticsNode :=
  { layout := default, props, texts, bounds := .zero, children := #[] }

#guard (text "hi").test (probe (texts := #["hi"]))
#guard !(text "hi").test (probe (texts := #["high"]))
#guard (text "hi").test (probe { editableText := some "hi" })
#guard (textContains "ell").test (probe { editableText := some "hello" })
#guard (tag "a").test (probe { testTag := some "a" })
#guard ((tag "a").or (tag "b")).test (probe { testTag := some "b" })
#guard !((tag "a").and (role .button)).test (probe { testTag := some "a" })
#guard (not (role .button)).test (probe (texts := #["x"]))
#guard (role .slider).test (probe { role := some .slider })

end Matcher

/-- All nodes matching `m`, in tree order (merged tree unless `unmerged`).
Mirrors `onAllNodes(matcher)`. -/
def findAll (m : Matcher) (unmerged : Bool := false) : TestM (Array SemanticsNode) := do
  let forest ← semanticsNodes unmerged
  return forest.foldl (fun acc r => acc ++ r.flatten.filter m.test) #[]

/-- Throw `msg` with the current semantics dump appended. -/
def failWithDump (msg : String) : TestM α := do
  throw (IO.userError s!"{msg}\nsemantics tree:\n{← semanticsDump}")

/-- The unique node matching `m`; throws (with the semantics dump) when there
are zero or several. Mirrors `onNode(matcher)` + `fetchSemanticsNode`. -/
def find (m : Matcher) (unmerged : Bool := false) : TestM SemanticsNode := do
  let hits ← findAll m unmerged
  if h : hits.size = 1 then
    return hits[0]
  else
    failWithDump s!"find: expected exactly one node matching {m.description}, \
                    found {hits.size}"

/-- The unique matching node's bounds in root (render-px) coordinates.
Mirrors `getUnclippedBoundsInRoot`. -/
def boundsOf (m : Matcher) : TestM Rect := do
  return (← find m).bounds

end Compose.Test

end
