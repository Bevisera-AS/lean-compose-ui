module

public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Runtime.Locals
public meta import Compose.Runtime.Locals
public import Compose.Ui.Overlay
public meta import Compose.Ui.Overlay

public section

namespace Compose

/-!
# Material-lite theme (`Compose/Material/Theme.lean`)

The trimmed Material3 theming system from DESIGN.md: `ColorScheme` (light and
dark baseline palettes), `Typography` (the type-scale roles the widgets
consume), `Shapes` (corner radii), `ThemeTokens` (interaction alphas,
elevations, surface materials, scrim opacity), and the `Theme` bundle tying
them together. `MaterialTheme` provides a bundle — or per-aspect overrides of
the ambient one — through CompositionLocals, re-providing `LocalTextStyle`
(so `Text` inside a themed subtree defaults to `bodyMedium` in `onSurface`)
and `LocalScrimColor` (so modal scrims follow the scheme).

Readers use the Compose-M3 spelling: `MaterialTheme.colorScheme`,
`MaterialTheme.typography`, `MaterialTheme.shapes`, `MaterialTheme.tokens`
(each a `Composable` reader rather than a bundle read, so recomposition
granularity follows what was actually read); `MaterialTheme.current`
rebundles the ambient aspects into a `Theme`. `LocalContentColor.current` is
the preferred content color established by `MaterialTheme`/`Surface`.

Omitted aspects **inherit**: `MaterialTheme (colors := some .dark) do …`
nested in a themed app keeps the outer typography/shapes/tokens (each
parameter is an `Option`; `none` reads the ambient value). At the root the
ambient values are the light-baseline defaults.

`LocalContentColor` lives here rather than in `Surface.lean` (where Compose
declares it) because `MaterialTheme` seeds it and Lean modules cannot import
cyclically — a documented, cosmetic deviation.
-/

/-- The Material3 color roles the framework consumes — trimmed to what the
widgets need, plus the surface-container tiers custom palettes layer with.
The tier and error-container fields default to derivations from the core
roles, so a custom scheme stays small: `{ ColorScheme.light with primary :=
…, surface := … }` fills the rest coherently. Mirrors
`androidx.compose.material3.ColorScheme`. -/
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
  outline : Color
  outlineVariant : Color
  error : Color
  onError : Color
  scrim : Color
  /-- Lowest-emphasis raised surface (sheets). Derived when unset. -/
  surfaceContainerLow : Color := Color.lerp surface onSurface 0.03
  /-- Mid-emphasis raised surface (menus, toolbars). Derived when unset. -/
  surfaceContainer : Color := Color.lerp surface onSurface 0.05
  /-- High-emphasis raised surface (dialogs). Derived when unset. -/
  surfaceContainerHigh : Color := Color.lerp surface onSurface 0.08
  /-- Error emphasis container (inline error chips/banners). Derived when
  unset. -/
  errorContainer : Color := Color.lerp error onError 0.85
  /-- Content on `errorContainer`. Derived when unset. -/
  onErrorContainer : Color := Color.lerp error Color.black 0.5
  deriving Repr, BEq

namespace ColorScheme

/-- The light palette. Material3 baseline structure, reseeded with a blue
primary in place of the M3 baseline purple; neutrals retinted from M3's
purple-leaning greys to cool blue-greys to match. Tier/error-container
roles use the derived defaults. -/
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
  outline := .hex 0xFF73777F
  outlineVariant := .hex 0xFFC3C6CF
  error := .hex 0xFFB3261E
  onError := .hex 0xFFFFFFFF
  scrim := .hex 0xFF000000

/-- The dark palette. Material3 baseline structure, reseeded with a blue
primary (an M3 dark-tone of the light scheme's blue) in place of the M3
baseline purple. Tier/error-container roles use the derived defaults. -/
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
  outline := .hex 0xFF8D9199
  outlineVariant := .hex 0xFF43474E
  error := .hex 0xFFF2B8B5
  onError := .hex 0xFF601410
  scrim := .hex 0xFF000000

instance : Inhabited ColorScheme := ⟨light⟩

/-- The `on*` role paired with a scheme color (`primary → onPrimary`, …), or
`none` for a color that is no scheme role. When a palette reuses one color
across roles the first match in the order below wins (primary family,
surface family, error family) — all three surface-container tiers map to
`onSurface`, so tier collisions are harmless by construction. Mirrors
`androidx.compose.material3.contentColorFor`. -/
def contentColorFor (cs : ColorScheme) (c : Color) : Option Color :=
  if c == cs.primary then some cs.onPrimary
  else if c == cs.primaryContainer then some cs.onPrimaryContainer
  else if c == cs.secondary then some cs.onSecondary
  else if c == cs.surface then some cs.onSurface
  else if c == cs.surfaceVariant then some cs.onSurfaceVariant
  else if c == cs.surfaceContainerLow then some cs.onSurface
  else if c == cs.surfaceContainer then some cs.onSurface
  else if c == cs.surfaceContainerHigh then some cs.onSurface
  else if c == cs.error then some cs.onError
  else if c == cs.errorContainer then some cs.onErrorContainer
  else none

#guard light.contentColorFor light.primary == some light.onPrimary
#guard light.contentColorFor light.surface == some light.onSurface
#guard light.contentColorFor light.surfaceContainerHigh == some light.onSurface
#guard dark.contentColorFor dark.error == some dark.onError
#guard dark.contentColorFor dark.errorContainer == some dark.onErrorContainer
#guard light.contentColorFor Color.magenta == none
-- A palette reusing one color across families resolves to the first family
-- in the `if`-chain (primary before surface here) — pinned, documented.
#guard let cs := { light with primary := light.surface }
       cs.contentColorFor cs.surface == some cs.onPrimary
#guard light != dark
-- Derived tiers sit strictly between `surface` and `onSurface`.
#guard light.surfaceContainer != light.surface
#guard dark.surfaceContainer != dark.surface

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

The Material3 interaction state-layer opacities (`md.sys.state.*`). The
loose `def`s are the baseline values; themes override them through
`ThemeTokens.interactions`. -/

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

/-! ## Theme tokens: interactions, elevations, materials -/

/-- Interaction-state opacities, consumed by `StateLayer` and the widgets'
disabled states. Defaults are the Material3 baseline tokens. -/
structure Interactions where
  hoverAlpha : Float32 := stateLayerHoverAlpha
  focusAlpha : Float32 := stateLayerFocusAlpha
  pressAlpha : Float32 := stateLayerPressAlpha
  disabledContentAlpha : Float32 := disabledContentAlpha
  disabledContainerAlpha : Float32 := disabledContainerAlpha
  deriving Repr, BEq, Inhabited

/-- Elevation (shadow) scale for the floating chrome. Defaults are the
per-component values the widgets historically hardcoded. -/
structure Elevations where
  card : Dp := 1
  tooltip : Dp := 2
  /-- Menus, menu-bar dropdowns, and the text-field selection toolbar. -/
  menu : Dp := 3
  dialog : Dp := 6
  deriving Repr, BEq, Inhabited

/-- The specular rim of a glass surface: a thin stroke whose brush is a
(unit-space) top-to-bottom highlight gradient. -/
structure RimSpec where
  width : Dp := 1
  /-- Unit-space brush (gradient geometry in the unit square, scaled to the
  surface at draw time). -/
  brush : Draw.Brush := .solid (Color.white.withAlpha 0.35)
  deriving Repr, BEq, Inhabited

/-- Everything a translucent "liquid glass" surface draws: a backdrop blur
radius, a translucent tint wash, a specular rim, and a soft drop shadow.
Data only — rendering (and light/dark-adaptive defaults) live in
`Compose.Material.Glass`; brushes are unit-space. -/
structure GlassSpec where
  /-- Unit-space translucent tint over the blurred backdrop. -/
  tint : Draw.Brush := .solid (Color.white.withAlpha 0.45)
  /-- Optional second unit-space wash painted between tint and rim (the
  light treatment's faint radial sheen). -/
  sheen : Option Draw.Brush := none
  /-- Backdrop Gaussian blur radius (σ = radius/2 px). -/
  blurRadius : Dp := 48
  /-- Refractive edge bend of the frost (`Modifier.backdropBlur`'s `refr`):
  the backdrop pulls inward like a lens near the rim. On by default — it is
  what makes glass read as glass rather than acrylic; set
  `{ strength := 0 }` for plain frost. -/
  refraction : BackdropRefraction := { strength := 6, band := 28 }
  rim : Option RimSpec := some {}
  elevation : Dp := 24
  deriving Repr, BEq, Inhabited

/-- How a themed container renders its background: classic opaque Material,
or translucent glass per a `GlassSpec`. -/
inductive SurfaceMaterial where
  | opaque
  | glass (spec : GlassSpec := {})
  deriving Repr, BEq, Inhabited

/-- Which widget classes render which `SurfaceMaterial`. -/
structure Materials where
  /-- Floating chrome: menus, dialogs, tooltips, sheets, cards, the
  selection toolbar. -/
  chrome : SurfaceMaterial := .opaque
  /-- Anchored bars: `TopAppBar`, the `MenuBar` strip. -/
  bars : SurfaceMaterial := .opaque
  deriving Repr, BEq, Inhabited

/-- The non-color, non-type, non-shape theme aspects: interaction alphas,
elevation scale, surface materials, and the modal scrim opacity. -/
structure ThemeTokens where
  interactions : Interactions := {}
  elevations : Elevations := {}
  materials : Materials := {}
  /-- Opacity applied to `colors.scrim` for modal scrims. -/
  scrimAlpha : Float32 := 0.32
  deriving Repr, BEq, Inhabited

/-- A complete theme: the bundle `MaterialTheme` installs and
`MaterialTheme.current` reads back. Swap wholesale
(`MaterialTheme (theme := some myTheme) do …`) or override aspects
(`MaterialTheme (colors := some .dark) do …` — omitted aspects inherit). -/
structure Theme where
  colors : ColorScheme := .light
  typography : Typography := {}
  shapes : Shapes := {}
  tokens : ThemeTokens := {}
  deriving Repr, BEq, Inhabited

/-- The light baseline theme. -/
def Theme.light : Theme := {}

/-- The dark baseline theme. -/
def Theme.dark : Theme := { colors := .dark }

#guard Theme.light != Theme.dark

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

/-- The ambient `ThemeTokens`. Static, one local for the whole group —
static-local invalidation is provider-subtree-wide on any change, so
per-aspect splitting buys nothing here. -/
initialize LocalTokens : CompositionLocal ThemeTokens ←
  staticCompositionLocalOf {}

/-- The preferred color for content (icons, hand-drawn marks) at this point
of the tree; seeded by `MaterialTheme` with `onSurface` and re-provided by
`Surface` to match its container color. Dynamic, so only actual readers
recompose. Mirrors `androidx.compose.material3.LocalContentColor` (declared
here, not in `Surface.lean` — see the module docstring). -/
initialize LocalContentColor : CompositionLocal Color ←
  compositionLocalOf Color.black

namespace MaterialTheme

/-- The ambient `ColorScheme`. Mirrors `MaterialTheme.colorScheme`. -/
def colorScheme : Composable ColorScheme := LocalColorScheme.current

/-- The ambient `Typography`. Mirrors `MaterialTheme.typography`. -/
def typography : Composable Typography := LocalTypography.current

/-- The ambient `Shapes`. Mirrors `MaterialTheme.shapes`. -/
def shapes : Composable Shapes := LocalShapes.current

/-- The ambient `ThemeTokens`. -/
def tokens : Composable ThemeTokens := LocalTokens.current

/-- The ambient theme, rebundled from the per-aspect locals. -/
def current : Composable Theme := do
  return { colors := ← LocalColorScheme.current
           typography := ← LocalTypography.current
           shapes := ← LocalShapes.current
           tokens := ← LocalTokens.current }

end MaterialTheme

/-- Provide a theme to `content`: the per-aspect CompositionLocals plus
`LocalScrimColor := colors.scrim` at the theme's scrim opacity,
`LocalContentColor := colors.onSurface`, and `LocalTextStyle :=
typography.bodyMedium` colored `onSurface` (so `Text` inside inherits the
themed default).

`theme` installs a whole bundle; the per-aspect parameters override it (or,
when `theme` is omitted, the **ambient** theme — so a nested
`MaterialTheme (colors := some .dark) do …` keeps the outer typography,
shapes, and tokens). Mirrors `androidx.compose.material3.MaterialTheme`. -/
def MaterialTheme (content : Composable Unit)
    (theme : Option Theme := none)
    (colors : Option ColorScheme := none) (typography : Option Typography := none)
    (shapes : Option Shapes := none) (tokens : Option ThemeTokens := none) :
    Composable Unit := do
  let base ← match theme with
    | some t => pure t
    | none => MaterialTheme.current
  let t : Theme :=
    { colors := colors.getD base.colors
      typography := typography.getD base.typography
      shapes := shapes.getD base.shapes
      tokens := tokens.getD base.tokens }
  CompositionLocalProvider LocalColorScheme t.colors <|
    CompositionLocalProvider LocalTypography t.typography <|
      CompositionLocalProvider LocalShapes t.shapes <|
        CompositionLocalProvider LocalTokens t.tokens <|
          CompositionLocalProvider LocalScrimColor
            (t.colors.scrim.withAlpha t.tokens.scrimAlpha) <|
            CompositionLocalProvider LocalContentColor t.colors.onSurface <|
              CompositionLocalProvider LocalTextStyle
                { t.typography.bodyMedium with color := t.colors.onSurface } content

end Compose

end
