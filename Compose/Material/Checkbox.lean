module

public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout

public section

namespace Compose

open Draw

/-!
# Checkbox (`Compose/Material/Checkbox.lean`)

A Material3 checkbox: an 18 dp box with 2 dp rounded corners inside a
40 dp touch target, toggled by click or Enter/Space when focused (via
`Modifier.clickable`), with a 20 dp-radius state-layer circle behind.
The container color animates `primary` ↔ transparent and the checkmark
(two `drawLine` strokes) scales in, both on 150 ms tweens. Disabled uses
the Material3 38 % content alpha. Mirrors
`androidx.compose.material3.Checkbox`.
-/

/-- The checkmark polyline as fractions of the 18 dp box (the Material check
glyph's three anchor points). -/
private def checkPoints : Array (Float32 × Float32) :=
  #[(0.229, 0.503), (0.40, 0.674), (0.771, 0.302)]

/-- Draw the checkbox visuals into the (touch-target-sized) node: centered
rounded box (animated `fill`, border fading out as `fraction` rises) and the
checkmark scaled about the box center by `fraction`. -/
private def drawCheckbox (fill : Color) (fraction : Float32)
    (borderColor markColor : Color) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let px (d : Dp) : Float32 := ctx.density.dpToPx d
  let box := px 18
  let c := sz.center
  let rect : Rect := ⟨c.x - box / 2, c.y - box / 2, c.x + box / 2, c.y + box / 2⟩
  let radius := px 2
  let w := px 2
  -- Fill (animated container color).
  if fill.a > 0.005 then
    DrawScope.drawRoundRect (.solid fill) (RoundRect.circular rect radius)
  -- Border, stroked just inside the box, fading as the fill takes over.
  let borderAlpha := borderColor.a * (1 - fraction)
  if borderAlpha > 0.005 then
    DrawScope.drawRoundRect (.solid (borderColor.withAlpha borderAlpha))
      (RoundRect.circular (rect.inflate (-w / 2)) (max 0 (radius - w / 2)))
      (.stroke w)
  -- Checkmark: two lines scaled about the box center.
  if fraction > 0.05 then
    let pt (fx fy : Float32) : Offset :=
      let p : Offset := ⟨rect.left + fx * box, rect.top + fy * box⟩
      c + (p - c) * fraction
    let (f0, f1, f2) := (checkPoints[0]!, checkPoints[1]!, checkPoints[2]!)
    let markW := px 2
    DrawScope.drawLine (.solid markColor) (pt f0.1 f0.2) (pt f1.1 f1.2) markW
    DrawScope.drawLine (.solid markColor) (pt f1.1 f1.2) (pt f2.1 f2.2) markW

/-- A Material checkbox (see the module docstring). `onCheckedChange`
receives the *new* value; toggle by click or Enter/Space when focused.
Mirrors `androidx.compose.material3.Checkbox`. -/
composable def Checkbox (checked : Bool) (onCheckedChange : Bool → IO Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let source ← rememberInteractionSource
  let latest ← rememberUpdatedRef (checked, onCheckedChange)
  -- The state-layer circle behind: radius 20 dp on the 40 dp target.
  let layer ← rememberStateLayer source .circle
    (tint := some (if checked then colors.primary else colors.onSurface))
    (enabled := enabled)
  let fillTarget :=
    if enabled then (if checked then colors.primary else colors.primary.withAlpha 0)
    else if checked then colors.onSurface.withAlpha disabledContentAlpha
    else Color.transparent
  let fill ← animateColorAsState fillTarget (.tween 150 0 .fastOutSlowIn)
  let fraction ← animateFloatAsState (if checked then 1.0 else 0.0)
    (.tween 150 0 .fastOutSlowIn)
  let fillNow ← fill.get
  let fractionNow ← fraction.get
  let borderColor := if enabled then colors.onSurfaceVariant
                     else colors.onSurface.withAlpha disabledContentAlpha
  let markColor := if enabled then colors.onPrimary else colors.surface
  let m := modifier
    |>.size 40 40
    |>.semantics (role := some .checkbox) (toggled := some checked)
    |>.clickable (do let (c, f) ← latest.get; f !c) enabled (source := some source)
    |>.then layer
    |>.drawBehind (drawCheckbox fillNow fractionNow borderColor markColor)
  Layout m .leaf

end Compose

end
