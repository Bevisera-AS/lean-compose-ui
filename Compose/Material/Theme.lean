module

public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Runtime.Locals
public meta import Compose.Runtime.Locals

public section

namespace Compose

/-!
# Material-lite theme (`Compose/Material/Theme.lean`)

The trimmed Material3 theming system from DESIGN.md: `ColorScheme` (light and
dark baseline palettes), `Typography` (the type-scale roles the widgets
consume), `Shapes` (corner radii), and the `MaterialTheme` provider that
carries all three through CompositionLocals — re-providing `LocalTextStyle`
so `Text` inside a themed subtree defaults to `bodyMedium` in `onSurface`.

Readers use the Compose-M3 spelling: `MaterialTheme.colorScheme`,
`MaterialTheme.typography`, `MaterialTheme.shapes` (each a `Composable`
reader rather than a `ThemeData` bundle, so recomposition granularity follows
what was actually read), plus `LocalContentColor.current` for the preferred
content color established by `MaterialTheme`/`Surface`.

`LocalContentColor` lives here rather than in `Surface.lean` (where Compose
declares it) because `MaterialTheme` seeds it and Lean modules cannot import
cyclically — a documented, cosmetic deviation.
-/

/-- The Material3 color roles the framework consumes (trimmed to what the
M9–M13 widgets need). Mirrors `androidx.compose.material3.ColorScheme`. -/
structure ColorScheme where
  primary : Color
  onPrimary : Color
  primaryContainer : Color
  onPrimaryContainer : Color
  secondary : Color
  onSecondary : Color
  surface : Color
  onSurface : Color
  surfaceVariant : Color
  onSurfaceVariant : Color
  background : Color
  onBackground : Color
  outline : Color
  outlineVariant : Color
  error : Color
  onError : Color
  scrim : Color
  deriving Repr, BEq

namespace ColorScheme

/-- The light palette. Material3 baseline structure, reseeded with a blue
primary in place of the M3 baseline purple; neutrals retinted from M3's
purple-leaning greys to cool blue-greys to match. -/
def light : ColorScheme where
  primary := .hex 0xFF386EE0
  onPrimary := .hex 0xFFFFFFFF
  primaryContainer := .hex 0xFFD5E1FF
  onPrimaryContainer := .hex 0xFF001A41
  secondary := .hex 0xFF56607A
  onSecondary := .hex 0xFFFFFFFF
  surface := .hex 0xFFFCFCFF
  onSurface := .hex 0xFF1A1C1E
  surfaceVariant := .hex 0xFFDFE2EB
  onSurfaceVariant := .hex 0xFF43474E
  background := .hex 0xFFFCFCFF
  onBackground := .hex 0xFF1A1C1E
  outline := .hex 0xFF73777F
  outlineVariant := .hex 0xFFC3C6CF
  error := .hex 0xFFB3261E
  onError := .hex 0xFFFFFFFF
  scrim := .hex 0xFF000000

/-- The dark palette. Material3 baseline structure, reseeded with a blue
primary (an M3 dark-tone of the light scheme's blue) in place of the M3
baseline purple. -/
def dark : ColorScheme where
  primary := .hex 0xFFABC7FF
  onPrimary := .hex 0xFF002E69
  primaryContainer := .hex 0xFF234787
  onPrimaryContainer := .hex 0xFFD5E1FF
  secondary := .hex 0xFFBEC6DC
  onSecondary := .hex 0xFF283041
  surface := .hex 0xFF1A1C1E
  onSurface := .hex 0xFFE2E2E6
  surfaceVariant := .hex 0xFF43474E
  onSurfaceVariant := .hex 0xFFC3C6CF
  background := .hex 0xFF1A1C1E
  onBackground := .hex 0xFFE2E2E6
  outline := .hex 0xFF8D9199
  outlineVariant := .hex 0xFF43474E
  error := .hex 0xFFF2B8B5
  onError := .hex 0xFF601410
  scrim := .hex 0xFF000000

instance : Inhabited ColorScheme := ⟨light⟩

/-- The `on*` role paired with a scheme color (`primary → onPrimary`, …), or
`none` for a color that is no scheme role. Mirrors
`androidx.compose.material3.contentColorFor`. -/
def contentColorFor (cs : ColorScheme) (c : Color) : Option Color :=
  if c == cs.primary then some cs.onPrimary
  else if c == cs.primaryContainer then some cs.onPrimaryContainer
  else if c == cs.secondary then some cs.onSecondary
  else if c == cs.surface then some cs.onSurface
  else if c == cs.surfaceVariant then some cs.onSurfaceVariant
  else if c == cs.background then some cs.onBackground
  else if c == cs.error then some cs.onError
  else none

#guard light.contentColorFor light.primary == some light.onPrimary
#guard light.contentColorFor light.surface == some light.onSurface
#guard dark.contentColorFor dark.error == some dark.onError
#guard light.contentColorFor Color.magenta == none
#guard light != dark

end ColorScheme

/-- The Material3 type-scale roles the widgets consume (trimmed): sizes,
line heights, and Roboto weights per the baseline tokens. Mirrors
`androidx.compose.material3.Typography`. -/
structure Typography where
  /-- Hero numerals/short strings. Mirrors `Typography.displayLarge`. -/
  displayLarge : TextStyle := { fontSize := 57, lineHeight := some 64 }
  /-- Section headlines. Mirrors `Typography.headlineMedium`. -/
  headlineMedium : TextStyle := { fontSize := 28, lineHeight := some 36 }
  /-- Dialog/card titles. Mirrors `Typography.titleLarge`. -/
  titleLarge : TextStyle := { fontSize := 22, lineHeight := some 28 }
  /-- List/menu titles. Mirrors `Typography.titleMedium`. -/
  titleMedium : TextStyle := { fontSize := 16, weight := .medium, lineHeight := some 24 }
  /-- Long-form body text. Mirrors `Typography.bodyLarge`. -/
  bodyLarge : TextStyle := { fontSize := 16, lineHeight := some 24 }
  /-- The default body text (what `MaterialTheme` seeds `LocalTextStyle`
  with). Mirrors `Typography.bodyMedium`. -/
  bodyMedium : TextStyle := { fontSize := 14, lineHeight := some 20 }
  /-- Button/label text. Mirrors `Typography.labelLarge`. -/
  labelLarge : TextStyle := { fontSize := 14, weight := .medium, lineHeight := some 20 }
  deriving Repr, BEq, Inhabited

#guard ({} : Typography).bodyMedium.fontSize == (14 : Sp)
#guard ({} : Typography).labelLarge.weight == FontWeight.medium

/-- The Material3 shape scale as resolved `Shape`s (corner radii per the
baseline tokens). Mirrors `androidx.compose.material3.Shapes`. -/
structure Shapes where
  /-- 4 dp corners. Mirrors `Shapes.extraSmall`. -/
  extraSmall : Shape := .rounded 4
  /-- 8 dp corners (buttons here — see `Button`). Mirrors `Shapes.small`. -/
  small : Shape := .rounded 8
  /-- 12 dp corners. Mirrors `Shapes.medium`. -/
  medium : Shape := .rounded 12
  /-- 16 dp corners. Mirrors `Shapes.large`. -/
  large : Shape := .rounded 16
  deriving Repr, BEq, Inhabited

#guard ({} : Shapes).extraSmall == Shape.rounded 4
#guard ({} : Shapes).large == Shape.rounded 16

/-! ## State-layer opacity tokens

The Material3 interaction state-layer opacities (`md.sys.state.*`), consumed
by `Compose.Material.StateLayer`. -/

/-- Hover state-layer opacity. Mirrors `md.sys.state.hover.state-layer-opacity`. -/
def stateLayerHoverAlpha : Float32 := 0.08

/-- Focus state-layer opacity. Mirrors `md.sys.state.focus.state-layer-opacity`. -/
def stateLayerFocusAlpha : Float32 := 0.10

/-- Press state-layer opacity. Mirrors `md.sys.state.pressed.state-layer-opacity`. -/
def stateLayerPressAlpha : Float32 := 0.10

/-- Content alpha of disabled widget content (labels, marks). Mirrors the
Material3 `38%` disabled-content token. -/
def disabledContentAlpha : Float32 := 0.38

/-- Container alpha of disabled widget containers. Mirrors the Material3
`12%` disabled-container token. -/
def disabledContainerAlpha : Float32 := 0.12

/-! ## CompositionLocals and the provider -/

/-- The ambient `ColorScheme`. Static: a theme swap recomposes the subtree.
Mirrors the internal `LocalColorScheme` of `androidx.compose.material3`. -/
initialize LocalColorScheme : CompositionLocal ColorScheme ←
  staticCompositionLocalOf .light

/-- The ambient `Typography`. Mirrors `material3`'s `LocalTypography`. -/
initialize LocalTypography : CompositionLocal Typography ←
  staticCompositionLocalOf {}

/-- The ambient `Shapes`. Mirrors `material3`'s `LocalShapes`. -/
initialize LocalShapes : CompositionLocal Shapes ←
  staticCompositionLocalOf {}

/-- The preferred color for content (icons, hand-drawn marks) at this point
of the tree; seeded by `MaterialTheme` with `onSurface` and re-provided by
`Surface` to match its container color. Dynamic, so only actual readers
recompose. Mirrors `androidx.compose.material3.LocalContentColor` (declared
here, not in `Surface.lean` — see the module docstring). -/
initialize LocalContentColor : CompositionLocal Color ←
  compositionLocalOf Color.black

/-- Provide the Material theme to `content`: `LocalColorScheme` /
`LocalTypography` / `LocalShapes`, `LocalContentColor := colors.onSurface`,
and `LocalTextStyle := typography.bodyMedium` colored `onSurface` (so `Text`
inside inherits the themed default). Nest with different `colors` for a
mixed-theme screen. Mirrors `androidx.compose.material3.MaterialTheme`. -/
def MaterialTheme (content : Composable Unit)
    (colors : ColorScheme := .light) (typography : Typography := {})
    (shapes : Shapes := {}) : Composable Unit :=
  CompositionLocalProvider LocalColorScheme colors <|
    CompositionLocalProvider LocalTypography typography <|
      CompositionLocalProvider LocalShapes shapes <|
        CompositionLocalProvider LocalContentColor colors.onSurface <|
          CompositionLocalProvider LocalTextStyle
            { typography.bodyMedium with color := colors.onSurface } content

namespace MaterialTheme

/-- The ambient `ColorScheme`. Mirrors `MaterialTheme.colorScheme`. -/
def colorScheme : Composable ColorScheme := LocalColorScheme.current

/-- The ambient `Typography`. Mirrors `MaterialTheme.typography`. -/
def typography : Composable Typography := LocalTypography.current

/-- The ambient `Shapes`. Mirrors `MaterialTheme.shapes`. -/
def shapes : Composable Shapes := LocalShapes.current

end MaterialTheme

end Compose

end
