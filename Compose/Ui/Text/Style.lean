module

public import Compose.Core.Density
public meta import Compose.Core.Density
public import Compose.Core.Color
public meta import Compose.Core.Color

public section

namespace Compose

/-!
# Text style (`Compose/Ui/Text/Style.lean`)

Pure, SDL-free description of how a run of text is drawn — font size, color,
weight, line height, and horizontal alignment. Mirrors
`androidx.compose.ui.text.TextStyle` (the subset the framework consumes),
`FontWeight`, and `TextAlign`.

`TextStyle.merge` defaults one style onto another (the ambient
`LocalTextStyle` under a caller's overrides), following Compose's rule that a
field left at its *unspecified* value (here: the struct default) inherits from
the base. This is the documented approximation of Compose's `Unspecified`
sentinels: a caller that explicitly asks for a value equal to the struct
default cannot distinguish it from "unspecified", so the base wins — fine in
practice, as themes rarely default to `14.sp`/black.
-/

/-- The three bundled Roboto weights. Mirrors the discrete
`androidx.compose.ui.text.font.FontWeight` values the default family ships
(`Normal` / `Medium` / `Bold`). -/
inductive FontWeight where
  | normal
  | medium
  | bold
  deriving Repr, BEq, Inhabited, Hashable, DecidableEq

namespace FontWeight

/-- The bundled Roboto file name for this weight (see `assets/fonts/`). -/
def fileName : FontWeight → String
  | .normal => "Roboto-Regular.ttf"
  | .medium => "Roboto-Medium.ttf"
  | .bold => "Roboto-Bold.ttf"

/-- A small stable index, used in cache keys. -/
def index : FontWeight → UInt64
  | .normal => 0
  | .medium => 1
  | .bold => 2

#guard FontWeight.normal.fileName == "Roboto-Regular.ttf"
#guard FontWeight.bold.fileName == "Roboto-Bold.ttf"

end FontWeight

/-- Horizontal alignment of a text block within its layout bounds. Mirrors
`androidx.compose.ui.text.style.TextAlign` (the `Start`/`Center`/`End`
subset; physical, no RTL resolution yet). -/
inductive TextAlign where
  | start
  | center
  | «end»
  deriving Repr, BEq, Inhabited, DecidableEq

/-- How a run of text is rendered. Mirrors the consumed subset of
`androidx.compose.ui.text.TextStyle`. Sizes are `Sp` (scaled to px through the
ambient `Density`), so glyphs stay crisp on HiDPI. -/
structure TextStyle where
  /-- Font size in `Sp`. Mirrors `TextStyle.fontSize`. -/
  fontSize : Sp := 14
  /-- Text color. Mirrors `TextStyle.color`. -/
  color : Color := Color.black
  /-- Font weight (selects the bundled Roboto file). Mirrors
  `TextStyle.fontWeight`. -/
  weight : FontWeight := .normal
  /-- Line height in `Sp`, or `none` to use the font's natural line spacing.
  Mirrors `TextStyle.lineHeight` (`none` ≈ `TextUnit.Unspecified`). -/
  lineHeight : Option Sp := none
  /-- Horizontal alignment within the layout bounds. Mirrors
  `TextStyle.textAlign`. -/
  align : TextAlign := .start
  deriving Repr, BEq, Inhabited

namespace TextStyle

/-- Overlay `override` onto `base`: fields of `override` left at the struct
default inherit from `base`; everything else wins. Mirrors `TextStyle.merge`
(with the struct default standing in for Compose's `Unspecified` — see the
module docstring). -/
def merge (base : TextStyle) (override : TextStyle) : TextStyle :=
  let d : TextStyle := {}
  { fontSize := if override.fontSize == d.fontSize then base.fontSize else override.fontSize
    color := if override.color == d.color then base.color else override.color
    weight := if override.weight == d.weight then base.weight else override.weight
    lineHeight := override.lineHeight <|> base.lineHeight
    align := if override.align == d.align then base.align else override.align }

-- merging the default onto a base is the base (identity of the default)
#guard TextStyle.merge { fontSize := 20, color := .red } {} == { fontSize := 20, color := .red }
-- a set field on `override` wins over `base`
#guard (TextStyle.merge { fontSize := 20 } { fontSize := 30 }).fontSize == (30 : Sp)
-- an unset field on `override` inherits from `base`
#guard (TextStyle.merge { color := .red } { fontSize := 30 }).color == Color.red
-- lineHeight inherits when `override` leaves it none, else wins
#guard (TextStyle.merge { lineHeight := some 24 } {}).lineHeight == some (24 : Sp)
#guard (TextStyle.merge { lineHeight := some 24 } { lineHeight := some 30 }).lineHeight == some (30 : Sp)
-- align inherits/overrides like a scalar field
#guard (TextStyle.merge { align := .center } {}).align == TextAlign.center
#guard (TextStyle.merge { align := .center } { align := .end }).align == TextAlign.end

end TextStyle

end Compose

end
