import Compose

/-!
# Liquid Glass (`lake exe demo-glass`)

The showcase for `Theme.liquidGlass`: a vivid scrolling backdrop under a
fixed glass toolbar and a floating glass panel (both `GlassSurface`,
frosting the content scrolling beneath them — true per-panel backdrop blur
on the GPU backend), an `ElevatedCard` rendering as glass purely through
the theme's `SurfaceMaterial` seam, and a glass dialog that additionally
frosts the whole window through the animated `blurBehind`. The toolbar
switch flips the whole subtree between the light and dark adaptive
treatments (`GlassSpec.forScheme`). Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-glass`.
-/

namespace Demos.Glass
open Compose

/-- Vivid gradient tiles — the backdrop the glass has something to tint
(and, for the dialog, frost) against. -/
composable def backdropSection : Composable Unit := do
  let pairs : List (Color × Color) :=
    [ (.hex 0xFFFF5E62, .hex 0xFFFF9966), (.hex 0xFF56CCF2, .hex 0xFF2F80ED),
      (.hex 0xFFA8E063, .hex 0xFF56AB2F), (.hex 0xFFDA22FF, .hex 0xFF9733EE),
      (.hex 0xFFF7971E, .hex 0xFFFFD200), (.hex 0xFFEC008C, .hex 0xFFFC6767),
      (.hex 0xFF00F260, .hex 0xFF0575E6), (.hex 0xFF8E2DE2, .hex 0xFF4A00E0) ]
  for (c0, c1) in pairs do
    Box (modifier := Modifier.fillMaxWidth |>.height 72
      |>.backgroundBrush (.gradient c0 c1 ⟨0, 0⟩ ⟨1, 1⟩) (.rounded 16))

/-- The fixed glass toolbar: title left, the light/dark treatment switch
right. A `GlassSurface`, so the tint/sheen/rim adapt to the ambient scheme. -/
composable def toolbarSection (dark : MutableState Bool) : Composable Unit := do
  GlassSurface (modifier := Modifier.fillMaxWidth) (shape := .rounded 18) do
    Row (modifier := Modifier.padding (horizontal := some 16) (vertical := some 10))
        (verticalAlignment := .centerVertically) do
      Text "Liquid Glass" (style := { fontSize := 18, weight := .medium })
      Spacer (Modifier.weight 1)
      Text (if ← dark.get then "dark" else "light") (style := { fontSize := 13 })
      Spacer (Modifier.width 8)
      Switch (← dark.get) dark.set

/-- The glass dialog: real frost via the animated `blurBehind`, content on a
`GlassSurface`. -/
composable def glassDialog (open' : MutableState Bool) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let spec := GlassSpec.forScheme colors
  if ← open'.get then
    Dialog (open'.set false) (blurBehind := spec.blurRadius) do
      GlassSurface (shape := .rounded 22) (spec := some spec) do
        Column (modifier := Modifier.padding (all := 20)) (verticalArrangement := .spacedBy 10) do
          Text "Glass dialog" (style := { fontSize := 17, weight := .medium })
          Text "The backdrop frosts in through the animated blur-behind."
            (style := { fontSize := 13 })
          Row (modifier := Modifier.fillMaxWidth) (horizontalArrangement := .«end») do
            TextButton (open'.set false) (Text "Close")

/-- The floating glass panel: a blurb plus the dialog trigger. -/
composable def panelSection (open' : MutableState Bool) : Composable Unit := do
  GlassSurface (shape := .rounded 18) do
    Column (modifier := Modifier.padding (all := 14)) (verticalArrangement := .spacedBy 8) do
      Text "Frosted panel" (style := { fontSize := 15, weight := .medium })
      Text "Frost, tint, sheen, and rim scale to any panel." (style := { fontSize := 12 })
      Button (open'.set true) (Text "Open glass dialog")

/-- The demo screen: scrolling backdrop, fixed glass toolbar (top), floating
glass panel (bottom), and — through the theme seam alone — a glass
`ElevatedCard` in the scroll. -/
composable def glassUi : Composable Unit := do
  let dark ← remember (mutableStateOf false)
  let open' ← remember (mutableStateOf false)
  let theme := Theme.liquidGlass (if ← dark.get then .dark else .light)
  MaterialTheme (theme := some theme) do
    syncWindowClearColor
    let scroll ← rememberScrollState
    Box (modifier := Modifier.fillMaxSize) do
      Column (modifier := (Modifier.fillMaxSize).padding (all := 16) |>.verticalScroll scroll)
          (verticalArrangement := .spacedBy 12) do
        Spacer (Modifier.height 48)
        backdropSection
        -- Through the SurfaceMaterial seam: chrome is glass in this theme.
        ElevatedCard (modifier := Modifier.fillMaxWidth) do
          Column (modifier := Modifier.padding (all := 14)) (verticalArrangement := .spacedBy 6) do
            Text "Card through the seam" (style := { fontSize := 15, weight := .medium })
            Text "This ElevatedCard renders as glass because the theme's \
                  chrome material says so — its code never mentions glass."
              (style := { fontSize := 12 })
        backdropSection
        Spacer (Modifier.height 88)
      Box (modifier := Modifier.align .topCenter |>.fillMaxWidth
          |>.padding (horizontal := some 12) (top := some 8)) do
        toolbarSection dark
      Box (modifier := Modifier.align .bottomCenter |>.padding (bottom := some 14)) do
        panelSection open'
      glassDialog open'

end Demos.Glass

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runMaterialApp "liquid glass" 480 560 Demos.Glass.glassUi
