module

public import Compose.Material.Surface
public meta import Compose.Material.Surface

public section

namespace Compose

/-!
# Card

Material 3 card containers — `Surface` presets with the medium shape:
filled (`surfaceVariant`-tinted container), elevated (surface + shadow),
outlined (surface + `outline` border). Mirrors
`androidx.compose.material3.Card`/`ElevatedCard`/`OutlinedCard` (static
containers; use a `Modifier.clickable` for actionable cards).
-/

/-- Filled card: a `surfaceVariant` container at the medium shape. -/
composable def Card (content : Composable Unit := pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Surface content modifier (shape := (← MaterialTheme.shapes).medium)
    (color := some colors.surfaceVariant)

/-- Elevated card: surface container with a 1dp shadow. -/
composable def ElevatedCard (content : Composable Unit := pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  Surface content modifier (shape := (← MaterialTheme.shapes).medium)
    (elevation := 1)

/-- Outlined card: surface container with an `outline` hairline. -/
composable def OutlinedCard (content : Composable Unit := pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Surface content modifier (shape := (← MaterialTheme.shapes).medium)
    (border := some { width := 1, color := colors.outline })

end Compose

end
