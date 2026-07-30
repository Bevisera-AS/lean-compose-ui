module

public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

namespace Compose

/-!
# Liquid-glass material (`Compose/Material/Glass.lean`)

The rendering half of `GlassSpec` (the data lives in `Theme.lean`): a
translucent panel treatment in the spirit of Apple's Liquid Glass — soft
drop shadow, a vertical translucent tint wash, an optional radial sheen,
and a thin specular rim, all clipped to a rounded shape. Brushes are
**unit-space** (`Brush.scaleTo` maps them onto each panel at draw time), so
one spec fits panels of any size.

Every glass panel frosts for real: the treatment slots a
`Modifier.backdropBlur` under the tint, so whatever is behind the panel in
its window renders Gaussian-blurred through the GPU backend's snapshot
split (σ = `blurRadius / 2` px, up to 64 — Phase B; the SDL backend keeps
the Phase-A tint-only degrade, and so does glass composited through an
offscreen layer, e.g. under a `Modifier.alpha` fade). Dialogs may still
pair with `blurBehind` when the *whole window* should frost, not just the
panel.

`GlassSpec.forScheme` picks light or dark treatment by the scheme's surface
luminance; `Theme.liquidGlass` bundles it into a complete theme whose
chrome and bars render as glass through the `SurfaceMaterial` seam.
-/

namespace GlassSpec

/-- Scheme-adaptive glass: picked by the **relative luminance of
`colors.surface`** (`≥ 0.5` = light treatment). Light glass is a white wash
fading down (α 0.55 → 0.30) with a faint top radial sheen and a bright
specular rim (white 0.60 → 0.08); dark glass is a near-`surface` smoke
deepening downward (α 0.35 → 0.55) with a dimmer rim (white 0.25 → 0.04)
and no sheen. All brushes unit-space. -/
def forScheme (colors : ColorScheme) : GlassSpec :=
  if colors.surface.luminance ≥ 0.5 then
    { tint := (.linearGradient
        #[(0, Color.white.withAlpha 0.55), (1, Color.white.withAlpha 0.30)]
        ⟨0.5, 0⟩ ⟨0.5, 1⟩)
      sheen := some (.radial (Color.white.withAlpha 0.18) (Color.white.withAlpha 0)
        ⟨0.5, 0⟩ 0.85)
      rim := some { brush := (.linearGradient
        #[(0, Color.white.withAlpha 0.60), (1, Color.white.withAlpha 0.08)]
        ⟨0.5, 0⟩ ⟨0.5, 1⟩) } }
  else
    { tint := (.linearGradient
        #[(0, colors.surface.withAlpha 0.35), (1, colors.surface.withAlpha 0.55)]
        ⟨0.5, 0⟩ ⟨0.5, 1⟩)
      rim := some { brush := (.linearGradient
        #[(0, Color.white.withAlpha 0.25), (1, Color.white.withAlpha 0.04)]
        ⟨0.5, 0⟩ ⟨0.5, 1⟩) } }

-- Light schemes get the white wash + sheen; dark schemes the surface smoke,
-- no sheen; both carry a rim.
#guard (forScheme .light).sheen.isSome && (forScheme .dark).sheen.isNone
#guard (forScheme .light).rim.isSome && (forScheme .dark).rim.isSome
#guard (forScheme .dark).tint
        == .linearGradient
            #[(0, (ColorScheme.dark.surface.withAlpha 0.35)),
              (1, (ColorScheme.dark.surface.withAlpha 0.55))] ⟨0.5, 0⟩ ⟨0.5, 1⟩

end GlassSpec

namespace Modifier

/-- The glass *background* chain (no clip — the `SurfaceMaterial` seam's
arm, where the caller owns border/clip): drop shadow (when the spec elevates)
→ backdrop frost (`Modifier.backdropBlur` at `blurRadius`, masked by
`shape`; GPU-only) → tint wash → optional sheen → specular rim, every brush
scaled from unit space at draw time. -/
def glassBackground (spec : GlassSpec := {}) (shape : Shape := .rounded 16)
    (m : Modifier := {}) : Modifier :=
  let m := if spec.elevation > 0 then m.shadow spec.elevation shape else m
  let m := if spec.blurRadius > 0 then m.backdropBlur spec.blurRadius shape else m
  let m := m.backgroundBrush spec.tint shape
  let m := match spec.sheen with
    | some b => m.backgroundBrush b shape
    | none => m
  match spec.rim with
  | some rim => m.borderBrush rim.width rim.brush shape
  | none => m

/-- The full glass treatment on one element: `glassBackground` plus a clip
of the content to `shape`. `Modifier.glass {} |>.padding …` on any Box makes
it a glass panel; `GlassSurface` adds the content-color contract. -/
def glass (spec : GlassSpec := {}) (shape : Shape := .rounded 16)
    (m : Modifier := {}) : Modifier :=
  glassBackground spec shape m |>.clip shape

-- The chain records shadow → backdrop frost → tint → sheen → rim → clip,
-- dropping the arms the spec omits (elevation 0, blurRadius 0, no sheen/rim).
#guard
  let spec : GlassSpec := { sheen := some (.solid .white), elevation := 2 }
  (Modifier.glass spec (.rounded 8)).elems ==
    #[.draw (.shadow 2 (.rounded 8) (Color.black.withAlpha 0.25)),
      .draw (.backdropBlur (GlassSpec.blurRadius {}) (.rounded 8)),
      .draw (.background spec.tint (.rounded 8)),
      .draw (.background (.solid .white) (.rounded 8)),
      .draw (.border 1 (RimSpec.brush {}) (.rounded 8)),
      .draw (.clip (.rounded 8))]
#guard (Modifier.glass { elevation := 0, rim := none, blurRadius := 0 } .circle).elems ==
    #[.draw (.background (GlassSpec.tint {}) .circle), .draw (.clip .circle)]

end Modifier

/-- A glass panel with `Surface`'s content-color contract: the treatment
comes from `spec` (default: `GlassSpec.forScheme` on the ambient scheme) and
content color defaults to the scheme's `onSurface` — the untinted role pair,
same rule as opaque surfaces (translucency is a treatment, not a role
change). The panel frosts its own backdrop (see `Modifier.glass`); pair
with `Popup`/`Dialog`'s `blurBehind` only when the whole window behind an
overlay should frost too. -/
def GlassSurface (content : Composable Unit := pure ())
    (modifier : Modifier := {}) (shape : Shape := .rounded 16)
    (spec : Option GlassSpec := none) (contentColor : Option Color := none) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let s := spec.getD (.forScheme colors)
  let resolvedContent := contentColor.getD colors.onSurface
  let ambientStyle ← LocalTextStyle.current
  Box (modifier := Modifier.glass s shape modifier) do
    CompositionLocalProvider LocalContentColor resolvedContent <|
      CompositionLocalProvider LocalTextStyle
        { ambientStyle with color := resolvedContent } content

/-- A complete Liquid-Glass theme over `colors`: floating chrome and bars
render as scheme-adaptive glass through the `SurfaceMaterial` seam; every
other aspect stays baseline Material. Install app-wide with
`runMaterialApp … (theme := .system (light := .liquidGlass .light)
(dark := .liquidGlass .dark))`. -/
def Theme.liquidGlass (colors : ColorScheme := .light) : Theme :=
  { colors
    tokens := { materials :=
      { chrome := .glass (.forScheme colors), bars := .glass (.forScheme colors) } } }

#guard (Theme.liquidGlass .dark).tokens.materials.chrome
        == .glass (.forScheme .dark)
#guard (Theme.liquidGlass .light).colors == ColorScheme.light

end Compose

end
