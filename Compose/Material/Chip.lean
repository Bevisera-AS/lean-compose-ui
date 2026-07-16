module

public import Compose.Material.Icons
public meta import Compose.Material.Icons
public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

namespace Compose

/-!
# FilterChip

The Material 3 selection chip: 32dp tall, small shape, outline when
unselected, `primaryContainer` fill plus a leading checkmark when selected
(this scheme carries no secondaryContainer role). Mirrors `androidx.compose.material3.FilterChip` (single- and
multi-select groups are app-land `Row`s of these).
-/

/-- A toggleable filter chip. -/
composable def FilterChip (selected : Bool) (onClick : IO Unit)
    (label : String) (modifier : Modifier := {}) (enabled : Bool := true) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let typo ← MaterialTheme.typography
  let shape := (← MaterialTheme.shapes).small
  let source ← rememberInteractionSource
  let clickRef ← rememberUpdatedRef onClick
  let contentColor :=
    if !enabled then colors.onSurface.withAlpha disabledContentAlpha
    else if selected then colors.onPrimaryContainer
    else colors.onSurfaceVariant
  let layer ← rememberStateLayer source shape (tint := some contentColor)
    (enabled := enabled)
  let m := modifier
    |>.sizeIn (minHeight := some 32)
    |>.semantics (role := some .checkbox) (toggled := some selected)
    |>.clickable (do (← clickRef.get)) enabled (source := some source)
    |>.background (if selected then colors.primaryContainer else .transparent) shape
    |>.then (if selected then {}
             else Modifier.border 1 colors.outline shape)
    |>.clip shape
    |>.then layer
    |>.padding (horizontal := some 12)
  Row (modifier := m) (horizontalArrangement := .spacedBy 8)
      (verticalAlignment := .centerVertically) do
    if selected then
      Icon Material.Icons.check (size := 18) (tint := some contentColor)
    CompositionLocalProvider LocalContentColor contentColor <|
      Text label (style := { typo.labelLarge with color := contentColor })

end Compose

end
