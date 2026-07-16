module

public import Compose.Material.Theme
public meta import Compose.Material.Theme
public import Compose.Ui.Draw.PathData
public meta import Compose.Ui.Draw.PathData
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout
public import Compose.Runtime.Macro
public meta import Compose.Runtime.Macro

public section

namespace Compose

/-!
# Icon

A path-based vector icon primitive: `IconVector` is a name plus `Path`s in
a square viewport (24 by convention — Material Symbols' export unit), drawn
scaled to the composable's size through the ordinary path tessellation and
tinted with `LocalContentColor` (so icons follow their `Surface`/button
content color for free). `Compose.Material.Icons` ships a small built-in
set; any Material icon is one `IconVector.ofPathData` paste away. Mirrors
`androidx.compose.material3.Icon` over an `ImageVector`-shaped asset.
-/

/-- A vector icon: filled `Path`s in a `viewport`-unit square. Build with
`IconVector.ofPathData` (panics at definition time on malformed data — icon
literals are vetted by their `#guard`s/first use, never at runtime). -/
structure IconVector where
  name : String
  path : Draw.Path
  viewport : Float32 := 24
  deriving Inhabited

namespace IconVector

/-- An icon from SVG path data (see `Draw.PathData.parse?`). Malformed data
degrades to an empty path — pair each definition with a `#guard
(icon.path.verbs.size > 0)` so bad pastes fail at compile time. -/
def ofPathData (name : String) (d : String) (viewport : Float32 := 24) :
    IconVector :=
  { name, path := (Draw.PathData.parse? d).getD {}, viewport }

end IconVector

/-- A tinted vector icon at `size` (Material's 24dp default). `tint`
defaults to the ambient content color; `contentDescription` feeds the
accessibility/semantics tree (`none` = decorative). -/
composable def Icon (icon : IconVector) (modifier : Modifier := {})
    (size : Dp := 24) (tint : Option Color := none)
    (contentDescription : Option String := none) : Composable Unit := do
  let color := tint.getD (← LocalContentColor.current)
  let m := modifier.size size size
    |>.semantics (desc := contentDescription)
    |>.drawBehind do
      let sz ← Draw.DrawScope.size
      Draw.DrawScope.drawPath (.solid color)
        (icon.path.scale (sz.width / icon.viewport))
  Layout m .leaf

end Compose

end
