module

public import Compose.Material.Icon
public meta import Compose.Material.Icon
public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Material.Surface
public meta import Compose.Material.Surface
public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

namespace Compose

/-!
# Scaffold + TopAppBar

App-screen chrome: `Scaffold` stacks an optional top bar, weighted content,
and an optional bottom bar in a background-colored `Column`; `TopAppBar` is
the small M3 variant (64dp: optional navigation icon, `titleLarge` title,
trailing actions). Insets: `Leandroid.runApp`'s default `safeAreaPadding`
already keeps the whole window clear of bars/cutouts, so `Scaffold` adds
none of its own; edge-to-edge apps (`safeArea := false`) should pad the
top bar with `LocalWindowInsets` themselves. No scroll-collapse behavior
(mirror of the *small* `androidx.compose.material3.TopAppBar` only).
-/

/-- Screen chrome: `topBar` / weighted `content` / `bottomBar` over the
theme background. -/
composable def Scaffold (content : Composable Unit := pure ())
    (modifier : Modifier := {})
    (topBar : Option (Composable Unit) := none)
    (bottomBar : Option (Composable Unit) := none) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Column (modifier := modifier.fillMaxSize |>.background colors.surface) do
    if let some bar := topBar then bar
    Box (modifier := Modifier.weight 1 |>.fillMaxWidth) do
      content
    if let some bar := bottomBar then bar

/-- The small M3 top app bar: 64dp, `navigationIcon` (usually an
`IconButton`-shaped clickable `Icon`), `titleLarge` title, `actions` row. -/
composable def TopAppBar (title : String) (modifier : Modifier := {})
    (navigationIcon : Option (Composable Unit) := none)
    (actions : Option (Composable Unit) := none) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let typo ← MaterialTheme.typography
  Surface (modifier := modifier.fillMaxWidth) (color := some colors.surface) do
    Row (modifier := Modifier.fillMaxWidth.height 64
          |>.padding (horizontal := some 8))
        (horizontalArrangement := .spacedBy 8)
        (verticalAlignment := .centerVertically) do
      if let some icon := navigationIcon then icon
      Text title (style := typo.titleLarge)
        (modifier := Modifier.weight 1)
      if let some acts := actions then acts

/-- A 40dp round clickable icon — the app-bar action shape. Mirrors
`androidx.compose.material3.IconButton`. -/
composable def IconButton (onClick : IO Unit) (icon : IconVector)
    (modifier : Modifier := {}) (enabled : Bool := true)
    (contentDescription : Option String := none) : Composable Unit := do
  let interactions := (← MaterialTheme.tokens).interactions
  let source ← rememberInteractionSource
  let clickRef ← rememberUpdatedRef onClick
  let layer ← rememberStateLayer source .circle (enabled := enabled)
  let contentColor ← LocalContentColor.current
  let m := modifier.size 40 40
    |>.semantics (role := some .button) (desc := contentDescription)
    |>.clickable (do (← clickRef.get)) enabled (source := some source)
    |>.clip .circle
    |>.then layer
  Box (modifier := m) (contentAlignment := .center) do
    Icon icon (tint := some (if enabled then contentColor
      else contentColor.withAlpha interactions.disabledContentAlpha))

end Compose

end
