import Compose.Material.Theme
import Compose.Foundation.Layouts

namespace Compose

/-!
# Surface (`Compose/Material/Surface.lean`)

The themed container primitive: a shaped, colored background (with optional
border), content clipped to the shape, and — the part every widget builds on
— the *content color contract*: `Surface` re-provides `LocalContentColor`
(and recolors `LocalTextStyle`) to the `on*` pair of its container color, so
text and marks inside automatically contrast with the container. Mirrors
`androidx.compose.material3.Surface` (shadow elevation via `Modifier.shadow`;
minus tonal overlays).

`LocalContentColor` itself is declared in `Theme.lean` (import-cycle
constraint, documented there).
-/

/-- A border stroke: width + color. Mirrors
`androidx.compose.foundation.BorderStroke`. -/
structure BorderStroke where
  width : Dp
  color : Color
  deriving Repr, BEq, Inhabited

/-- A shaped, colored container providing the content color for what's
inside. `color` defaults to the theme's `surface`; `contentColor` defaults to
the scheme's `on*` pair for `color` (or the ambient content color when
`color` is no scheme role). Content is clipped to `shape`; `elevation > 0`
draws a Material drop shadow under the shape (`Modifier.shadow`). Mirrors
`androidx.compose.material3.Surface` (shadow elevation; no tonal overlays). -/
def Surface (content : Composable Unit := pure ())
    (modifier : Modifier := {}) (shape : Shape := .rectangle)
    (color : Option Color := none) (contentColor : Option Color := none)
    (border : Option BorderStroke := none) (elevation : Dp := 0) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let ambientContent ← LocalContentColor.current
  let container := color.getD colors.surface
  let resolvedContent := contentColor.getD
    ((colors.contentColorFor container).getD ambientContent)
  let m := (if elevation > 0 then modifier.shadow elevation shape else modifier)
    |>.background container shape
    |>.then (match border with
             | some b => Modifier.border b.width b.color shape
             | none => {})
    |>.clip shape
  let ambientStyle ← LocalTextStyle.current
  Box (modifier := m) do
    CompositionLocalProvider LocalContentColor resolvedContent <|
      CompositionLocalProvider LocalTextStyle
        { ambientStyle with color := resolvedContent } content

end Compose
