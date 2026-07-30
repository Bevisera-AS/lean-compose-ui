module

public import Compose.Material.Surface
public meta import Compose.Material.Surface
public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer

public section

namespace Compose

/-!
# Buttons (`Compose/Material/Button.lean`)

`Button` (filled), `OutlinedButton`, and `TextButton`, mirroring their
`androidx.compose.material3` namesakes on the M9 diet: labelLarge content,
`shapes.small` corners (a documented deviation from M3's fully-rounded pill),
40 dp min height, 24 dp horizontal content padding (12 dp for `TextButton`),
hover/focus/press state layers + bounded press ripple, keyboard activation
via `Modifier.clickable` (Enter/Space when focused), and a focus ring drawn
in `outline` when focused (inside the bounds — no outside-bounds drawing in
the M9 renderer). Disabled buttons use the Material3 38 % content / 12 %
container alphas and leave the focus order.
-/

/-- Shared button chassis: interaction wiring, container, focus ring, state
layer, padding, centered `labelLarge` content. -/
private def buttonImpl (onClick : IO Unit) (modifier : Modifier) (enabled : Bool)
    (container contentColor : Color) (border : Option BorderStroke)
    (horizontalPadding : Dp) (content : Composable Unit) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let typo ← MaterialTheme.typography
  let shape := (← MaterialTheme.shapes).small
  let source ← rememberInteractionSource
  let focused ← source.focused.get
  -- Read the latest onClick at activation time: the tap coroutine inside
  -- `clickable` relaunches on key change only (see `rememberUpdatedRef`).
  let clickRef ← rememberUpdatedRef onClick
  let layer ← rememberStateLayer source shape (tint := some contentColor) (enabled := enabled)
  let m := modifier
    |>.sizeIn (minWidth := some 64) (minHeight := some 40)
    |>.semantics (role := some .button)
    |>.clickable (do (← clickRef.get)) enabled (source := some source)
    |>.background container shape
    |>.border 2 (if focused && enabled then colors.outline else .transparent) shape
    |>.then (match border with
             | some b => Modifier.border b.width b.color shape
             | none => {})
    |>.clip shape
    |>.then layer
    |>.padding (horizontal := some horizontalPadding) (vertical := some 8)
  Box (modifier := m) (contentAlignment := .center) do
    CompositionLocalProvider LocalContentColor contentColor <|
      CompositionLocalProvider LocalTextStyle
        { typo.labelLarge with color := contentColor } content

/-- Filled button: `primary` container, `onPrimary` content. Mirrors
`androidx.compose.material3.Button`. -/
composable def Button (onClick : IO Unit) (content : Composable Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let interactions := (← MaterialTheme.tokens).interactions
  buttonImpl onClick modifier enabled
    (container := if enabled then colors.primary
                  else colors.onSurface.withAlpha interactions.disabledContainerAlpha)
    (contentColor := if enabled then colors.onPrimary
                     else colors.onSurface.withAlpha interactions.disabledContentAlpha)
    (border := none) (horizontalPadding := 24) content

/-- Outlined button: transparent container, 1 dp `outline` border, `primary`
content. Mirrors `androidx.compose.material3.OutlinedButton`. -/
composable def OutlinedButton (onClick : IO Unit) (content : Composable Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let interactions := (← MaterialTheme.tokens).interactions
  buttonImpl onClick modifier enabled
    (container := .transparent)
    (contentColor := if enabled then colors.primary
                     else colors.onSurface.withAlpha interactions.disabledContentAlpha)
    (border := some { width := 1
                      color := if enabled then colors.outline
                               else colors.onSurface.withAlpha
                                 interactions.disabledContainerAlpha })
    (horizontalPadding := 24) content

/-- Text button: no container or border, `primary` content, tighter padding.
Mirrors `androidx.compose.material3.TextButton`. -/
composable def TextButton (onClick : IO Unit) (content : Composable Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let interactions := (← MaterialTheme.tokens).interactions
  buttonImpl onClick modifier enabled
    (container := .transparent)
    (contentColor := if enabled then colors.primary
                     else colors.onSurface.withAlpha interactions.disabledContentAlpha)
    (border := none) (horizontalPadding := 12) content

end Compose

end
