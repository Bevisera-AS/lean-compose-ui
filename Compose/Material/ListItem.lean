module

public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

namespace Compose

/-!
# ListItem

The Material 3 list row: leading slot, headline + optional supporting
text, trailing slot, with M3's paddings and type roles. Mirrors
`androidx.compose.material3.ListItem` (one- and two-line layouts; no
overline or three-line variant).
-/

/-- A list row. `headline` is required; `supporting` adds the second line;
`leading`/`trailing` are free-form slots (icons, switches, checkboxes). -/
composable def ListItem (headline : String)
    (modifier : Modifier := {}) (supporting : Option String := none)
    (leading : Option (Composable Unit) := none)
    (trailing : Option (Composable Unit) := none) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let typo ← MaterialTheme.typography
  Row (modifier := modifier.fillMaxWidth
        |>.padding (horizontal := some 16) (vertical := some 8)
        |>.sizeIn (minHeight := some (if supporting.isSome then 72 else 56)))
      (horizontalArrangement := .spacedBy 16)
      (verticalAlignment := .centerVertically) do
    if let some slot := leading then slot
    Column (modifier := Modifier.weight 1) do
      Text headline (style := typo.bodyLarge)
      if let some s := supporting then
        Text s (style := { typo.bodyMedium with color := colors.onSurfaceVariant })
    if let some slot := trailing then slot

end Compose

end
