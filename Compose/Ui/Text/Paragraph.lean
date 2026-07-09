import Compose.Ui.Text.Fonts
import Compose.Ui.Draw.Scope

namespace Compose

open Sdl.Ttf (Font Text TextEngine)

/-!
# Text layout (`Compose/Ui/Text/Paragraph.lean`)

`TextLayout` wraps a live `Ttf.Text` on the window's **renderer text engine**
together with its resolved font and the inputs that produced it (string, style,
density, wrap width). Mirrors `androidx.compose.ui.text.TextLayoutResult` /
`Paragraph` — the shaped, measurable, drawable text a `Text` node owns.

The `Ttf.Text` is a mutable, atlas-cached object: `update` diffs the new inputs
against the last ones and touches it only where they differ (`setString`,
`setColor`, `setFont`, `setWrapWidth`), so unchanged text is never re-shaped
(Compose's layout cache). The `Ttf.Text` stays alive as a field of the layout
(which the `Text` node remembers); `destroy` releases it on forget.

Byte offsets in the caret/hit helpers are **UTF-8 byte offsets** into the
string (SDL_ttf's native unit), matching the model M11's `TextField` edits.
-/

/-- Convert a `Compose.Color` to SDL's byte-channel `Sdl.Color`. -/
private def colorToSdl (c : Color) : Sdl.Color :=
  let (r, g, b, a) := c.toBytes
  ⟨r, g, b, a⟩

/-- The inputs baked into a `TextLayout`'s current `Ttf.Text` state. -/
structure TextLayoutState where
  string : String
  style : TextStyle
  density : Density
  /-- Wrap width last applied to the `Ttf.Text` (`0` = wrap on newlines only). -/
  wrapWidth : Int32
  /-- The currently resolved font (its `lineSkip` gives the natural line height). -/
  font : Font

/-- A shaped, measurable, drawable run of text over a renderer text engine.
Mirrors `androidx.compose.ui.text.Paragraph`. -/
structure TextLayout where
  /-- The font store used to (re)resolve the typeface on size/weight/density
  change. -/
  store : FontStore
  /-- The live SDL text object (pins its engine and font by reference count). -/
  text : Text
  /-- The inputs currently baked into `text`. -/
  state : IO.Ref TextLayoutState
  /-- Count of actual `Ttf.Text` mutations (a test probe for the layout cache). -/
  mutations : IO.Ref Nat

namespace TextLayout

private def bump (tl : TextLayout) : IO Unit := tl.mutations.modify (· + 1)

/-- Create a layout for `text` in `style` at `density`, laid out by `engine`.
Mirrors `Paragraph(...)` construction. -/
def create (engine : TextEngine) (store : FontStore) (text : String) (style : TextStyle)
    (density : Density) : IO TextLayout := do
  let font ← store.resolve style density
  let t ← engine.createText font text
  t.setColor (colorToSdl style.color)
  let state ← IO.mkRef { string := text, style, density, wrapWidth := 0, font }
  return { store, text := t, state, mutations := ← IO.mkRef 0 }

/-- Reconcile the layout to new inputs, touching the `Ttf.Text` only where they
changed: the font is re-resolved (and `setFont`) on a size/weight/density
change, then `setString`/`setColor` as needed. Mirrors reusing a cached
`TextLayoutResult` when inputs are unchanged. -/
def update (tl : TextLayout) (text : String) (style : TextStyle) (density : Density) :
    IO Unit := do
  let st ← tl.state.get
  let mut font := st.font
  if style.fontSize != st.style.fontSize || style.weight != st.style.weight
      || density != st.density then
    font ← tl.store.resolve style density
    tl.text.setFont font
    tl.bump
  if text != st.string then
    tl.text.setString text
    tl.bump
  if style.color != st.style.color then
    tl.text.setColor (colorToSdl style.color)
    tl.bump
  tl.state.set { st with string := text, style, density, font }

/-- Measure the text, wrapping to `maxWidth` px when bounded (`none` = no wrap,
newlines only). Returns the shaped `(width, height)`. Mirrors measuring a
`Paragraph` against a width constraint. -/
def measure (tl : TextLayout) (maxWidth : Option Int32) : IO IntSize := do
  let desired := match maxWidth with | some w => max 0 w | none => 0
  let st ← tl.state.get
  if desired != st.wrapWidth then
    tl.text.setWrapWidth desired
    tl.state.set { st with wrapWidth := desired }
    tl.bump
  let (w, h) ← tl.text.size
  return ⟨w, h⟩

/-- Draw the text with its top-left at `topLeft` (local coordinates), honoring
the ambient `DrawContext` translation and alpha. Mirrors `DrawScope.drawText`. -/
def draw (tl : TextLayout) (topLeft : Offset) : Draw.DrawM Unit := do
  let ctx ← read
  let st ← tl.state.get
  let c := st.style.color
  tl.text.setColorFloat ⟨c.r, c.g, c.b, c.a * ctx.alpha⟩
  let p := topLeft + ctx.translation
  tl.text.drawRenderer p.x p.y

/-- The line height in px: the style's explicit `lineHeight` if set, else the
font's natural line spacing. Mirrors `TextLayoutResult` line metrics. -/
def lineHeight (tl : TextLayout) : IO Int32 := do
  let st ← tl.state.get
  match st.style.lineHeight with
  | some sp => return (st.density.spToPx sp + 0.5).floor.toInt32
  | none => st.font.lineSkip

/-- The UTF-8 byte offset of the character nearest local point `p`. Drives
click-to-caret in M11's `TextField`. Mirrors `MultiParagraph.getOffsetForPosition`. -/
def hitToByteOffset (tl : TextLayout) (p : Offset) : IO Nat := do
  let sub ← tl.text.subStringForPoint p.x.toInt32 p.y.toInt32
  return sub.offset.toNatClampNeg

/-- The bounding rect (local coordinates) of the substring at UTF-8 byte
`off`. Drives caret geometry in M11. Mirrors `MultiParagraph.getBoundingBox`. -/
def byteOffsetToRect (tl : TextLayout) (off : Nat) : IO Rect := do
  let sub ← tl.text.subString (Int32.ofNat off)
  let r := sub.rect
  return ⟨r.x.toFloat32, r.y.toFloat32, (r.x + r.w).toFloat32, (r.y + r.h).toFloat32⟩

/-- Destroy the underlying `Ttf.Text` (call on forget). -/
def destroy (tl : TextLayout) : IO Unit := tl.text.destroy

/-- Number of `Ttf.Text` mutations so far (a test probe). -/
def mutationCount (tl : TextLayout) : IO Nat := tl.mutations.get

end TextLayout

end Compose
