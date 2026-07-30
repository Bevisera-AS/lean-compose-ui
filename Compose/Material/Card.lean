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
    (material := some (← MaterialTheme.tokens).materials.chrome)

/-- Elevated card: surface container with the theme's card shadow. -/
composable def ElevatedCard (content : Composable Unit := pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  let tokens ← MaterialTheme.tokens
  Surface content modifier (shape := (← MaterialTheme.shapes).medium)
    (elevation := tokens.elevations.card) (material := some tokens.materials.chrome)

/-- Outlined card: surface container with an `outline` hairline. -/
composable def OutlinedCard (content : Composable Unit := pure ())
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Surface content modifier (shape := (← MaterialTheme.shapes).medium)
    (border := some { width := 1, color := colors.outline })
    (material := some (← MaterialTheme.tokens).materials.chrome)

end Compose

end
