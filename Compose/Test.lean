module

public import Compose.Test.Semantics
public meta import Compose.Test.Semantics
public import Compose.Test.Harness
public meta import Compose.Test.Harness
public import Compose.Test.Finders
public meta import Compose.Test.Finders
public import Compose.Test.Actions
public meta import Compose.Test.Actions
public import Compose.Test.Assertions
public meta import Compose.Test.Assertions

public section

/-!
# `Compose.Test` — the UI test framework (milestone MT)

The `androidx.compose.ui.test` analog, Lean-shaped: `open Compose.Test`,
boot a UI with `runComposeTest`, and drive it in `TestM` do-notation —
matchers are anonymous-constructor literals, actions and assertions are
verbs taking the matcher first, and time only moves when the test says so.

```lean
open Compose.Test in
runComposeTest counterApp do
  assertExists (.text "Count: 0")
  click (.text "Increment")                -- real SDL events, real hit test
  assertExists (.text "Count: 1")
  typeText (.role .textField) "hello"      -- click-to-focus + IME commits
  assertTextEquals (.role .textField) "hello"
  advanceTimeBy 150                        -- drive animations by hand
  assertRangeValue (.tag "progress") 0.5
```

Layering: this framework lives *above* material (it imports the theme for
`runComposeTest`'s default wrap); widgets know nothing about it beyond the
`Modifier.semantics` properties they publish. See `AGENTS.md` (Testing) for
the how-to and `docs/DESIGN.md` for the design.
-/

end
