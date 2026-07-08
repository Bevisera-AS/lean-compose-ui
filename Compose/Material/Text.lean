import Compose.Ui.Window
import Compose.Ui.Layout
import Compose.Runtime.Macro

namespace Compose

open Draw

/-!
# Text composable (`Compose/Material/Text.lean`)

`Text` — the leaf that shapes, measures, and draws a run of text. Mirrors
`androidx.compose.material.Text` (the thin wrapper over the foundation
`BasicText`): it remembers a `TextLayout`, reconciles it against the current
string/style/density, measures its intrinsic size clamped to the incoming
constraints, and draws it (aligned within the node box) behind any content.

`LocalTextStyle` supplies the ambient default style; a caller's `style` merges
onto it (`TextStyle.merge`), and an explicit `color` overrides `style.color`.
M9's Material theme re-provides `LocalTextStyle` with its typography; until then
its default is the plain `TextStyle` default (`14.sp`, black, normal).
-/

/-- The ambient default text style, merged under each `Text`'s own `style`.
Static: a theme change re-provides it and recomposes the subtree. Mirrors
`androidx.compose.material.LocalTextStyle` (default: the `TextStyle` default). -/
initialize LocalTextStyle : CompositionLocal TextStyle ← staticCompositionLocalOf {}

/-- Resolve the effective style: the ambient default with the caller's `style`
merged on top, then an explicit `color` override. -/
private def resolveTextStyle (ambient style : TextStyle) (color : Option Color) : TextStyle :=
  let base := ambient.merge style
  match color with
  | some c => { base with color := c }
  | none => base

/-- Horizontal offset of `inner`-wide text within an `outer`-wide box. -/
private def alignDx (align : TextAlign) (outer inner : Int32) : Int32 :=
  match align with
  | .start => 0
  | .center => (outer - inner) / 2
  | .«end» => outer - inner

#guard alignDx .start 100 40 == 0
#guard alignDx .center 100 40 == 30
#guard alignDx .«end» 100 40 == 60

/-- A stable identity for a resolved `TextStyle` (feeds the measure policy's
`policyInputs` so unchanged text skips re-measure). -/
private def styleKey (s : TextStyle) : UInt64 :=
  let c := s.color
  let alignK : UInt64 := match s.align with | .start => 0 | .center => 1 | .«end» => 2
  let lineK : UInt64 := match s.lineHeight with
    | none => 0
    | some sp => mixKeys 0x11 sp.value.toBits.toUInt64
  mixKeys s.weight.index <| mixKeys s.fontSize.value.toBits.toUInt64 <|
    mixKeys c.r.toBits.toUInt64 <| mixKeys c.g.toBits.toUInt64 <|
    mixKeys c.b.toBits.toUInt64 <| mixKeys c.a.toBits.toUInt64 <|
    mixKeys alignK lineK

/-- A stable identity for a density (scale + font scale). -/
private def densityKey (d : Density) : UInt64 :=
  mixKeys d.density.toBits.toUInt64 d.fontScale.toBits.toUInt64

/-- Get (creating on first use) and reconcile the layout stored in `cell`. Kept
out of the composable so the `composable` macro never keys its IO control flow. -/
private def obtainLayout (cell : IO.Ref (Option TextLayout)) (tc : TextContext)
    (text : String) (style : TextStyle) (density : Density) : IO TextLayout := do
  match ← cell.get with
  | some l =>
    l.update text style density
    return l
  | none =>
    let l ← TextLayout.create tc.textEngine tc.fontStore text style density
    cell.set (some l)
    return l

/-- Display a run of text. `color` overrides `style.color`; `style` merges onto
the ambient `LocalTextStyle`. The node measures to the text's intrinsic size
(wrapped when the incoming width is bounded), clamped to the constraints, and
draws the glyphs aligned within its box per `style.align`. Mirrors
`androidx.compose.material.Text`. -/
composable def Text (text : String) (modifier : Modifier := {})
    (style : TextStyle := {}) (color : Option Color := none) : Composable Unit := do
  let ambient ← LocalTextStyle.current
  let density ← LocalDensity.current
  let tc? ← LocalTextContext.current
  -- Semantics: the displayed run, findable by `Matcher.text` (published even
  -- outside a window so plain-composition tests see it).
  let modifier := modifier.semantics (text := some text)
  match tc? with
  | none =>
    -- Composed outside a window (no text stack): occupy no space.
    Layout modifier .leaf (policyInputs := some 0)
  | some tc =>
    let resolved := resolveTextStyle ambient style color
    let cell ← remember (IO.mkRef (none : Option TextLayout))
    let alignRef ← remember (IO.mkRef IntOffset.zero)
    let layout ← obtainLayout cell tc text resolved density
    let policy : MeasurePolicy := fun _ _ c => do
      let maxW := if c.hasBoundedWidth then some c.maxWidth else none
      let sz ← layout.measure maxW
      let outSize := c.constrain sz
      alignRef.set ⟨max 0 (alignDx resolved.align outSize.width sz.width), 0⟩
      return { size := outSize }
    let drawMod := modifier.drawBehind do
      let off ← alignRef.get
      layout.draw off.toOffset
    Layout drawMod policy
      (policyInputs := some
        (mixKeys (stringKey text) (mixKeys (styleKey resolved) (densityKey density))))

end Compose
