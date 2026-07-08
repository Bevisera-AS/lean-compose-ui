import Compose.Material.Theme
import Compose.Ui.Layout

namespace Compose

/-!
# Divider (`Compose/Material/Divider.lean`)

A thin full-width rule in `outlineVariant`. Mirrors
`androidx.compose.material3.HorizontalDivider`.
-/

/-- A horizontal rule filling the available width. `color` defaults to the
theme's `outlineVariant`. Mirrors
`androidx.compose.material3.HorizontalDivider`. -/
composable def HorizontalDivider (modifier : Modifier := {}) (thickness : Dp := 1)
    (color : Option Color := none) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Layout (modifier |>.fillMaxWidth |>.height thickness
    |>.background (color.getD colors.outlineVariant)) .leaf

end Compose
