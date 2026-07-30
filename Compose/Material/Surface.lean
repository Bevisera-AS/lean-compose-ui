module

public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Material.Glass
public meta import Compose.Material.Glass
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

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

/-- The shadow + background chain of a themed container, appended to `base`:
the drop shadow (only when `elevation > 0`) then the container fill clipped to
`shape`. The single seam every themed container's background goes through, so
a `SurfaceMaterial` swap reaches widgets that build their background from raw
modifiers as well as those that use `Surface`.

`.glass` renders the spec's translucent treatment (`Modifier.glassBackground`
— tint wash, sheen, rim; `Compose.Material.Glass`) instead of the opaque
fill, with the *widget's* elevation replacing the spec's own (chrome keeps
its Material shadow scale; the spec elevation is for standalone panels).
The container `color` is ignored by design — content-color resolution still
runs on it (see `Surface`). -/
def SurfaceMaterial.backgroundModifier (m : SurfaceMaterial) (color : Color)
    (shape : Shape) (elevation : Dp) (base : Modifier := {}) : Modifier :=
  match m with
  | .opaque =>
    (if elevation > 0 then base.shadow elevation shape else base)
      |>.background color shape
  | .glass spec => Modifier.glassBackground { spec with elevation } shape base

/-- A shaped, colored container providing the content color for what's
inside. `color` defaults to the theme's `surface`; `contentColor` defaults to
the scheme's `on*` pair for `color` (or the ambient content color when
`color` is no scheme role). Content is clipped to `shape`; `elevation > 0`
draws a Material drop shadow under the shape (`Modifier.shadow`).

`material` picks how the background renders (`none` = `.opaque`); widgets that
are themed chrome pass `(← MaterialTheme.tokens).materials.chrome`/`.bars`.
**The content color is independent of it**: resolution always runs on the
untinted role `color`, because translucency is a rendering treatment, not a
role change — a glass `surfaceContainer` still contrasts against `onSurface`.

Mirrors `androidx.compose.material3.Surface` (shadow elevation; no tonal
overlays). -/
def Surface (content : Composable Unit := pure ())
    (modifier : Modifier := {}) (shape : Shape := .rectangle)
    (color : Option Color := none) (contentColor : Option Color := none)
    (border : Option BorderStroke := none) (elevation : Dp := 0)
    (material : Option SurfaceMaterial := none) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let ambientContent ← LocalContentColor.current
  let container := color.getD colors.surface
  let resolvedContent := contentColor.getD
    ((colors.contentColorFor container).getD ambientContent)
  let m := (material.getD .opaque).backgroundModifier container shape elevation modifier
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

end
