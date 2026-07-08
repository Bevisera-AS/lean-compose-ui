import Compose.Material.StateLayer
import Compose.Ui.Layout

namespace Compose

open Draw

/-!
# RadioButton (`Compose/Material/RadioButton.lean`)

The standard two-circle radio: a 20 dp ring (2 dp stroke) inside a 40 dp
touch target, with the inner dot scaling in (spring-free 150 ms tween on its
`Dp` radius) when selected. Selection by click or Enter/Space when focused;
a 20 dp state-layer circle behind. Disabled uses the Material3 38 % alpha.
Mirrors `androidx.compose.material3.RadioButton`.
-/

/-- Draw the ring and the (animated-radius) inner dot, centered. -/
private def drawRadio (ringColor dotColor : Color) (dotRadius : Dp) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let px (d : Dp) : Float32 := ctx.density.dpToPx d
  let c := sz.center
  DrawScope.drawCircle (.solid ringColor) c (px 9) (.stroke (px 2))
  let r := px dotRadius
  if r > 0.5 then
    DrawScope.drawCircle (.solid dotColor) c r

/-- A Material radio button (see the module docstring). `onClick` fires on
activation regardless of the current `selected` (group logic belongs to the
caller, as in Compose). Mirrors `androidx.compose.material3.RadioButton`. -/
composable def RadioButton (selected : Bool) (onClick : IO Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let source ← rememberInteractionSource
  let clickRef ← rememberUpdatedRef onClick
  let layer ← rememberStateLayer source .circle
    (tint := some (if selected then colors.primary else colors.onSurface))
    (enabled := enabled)
  -- Inner dot: 10 dp diameter when selected, gone otherwise.
  let dotRadius ← animateDpAsState (if selected then 5 else 0) (.tween 150 0 .fastOutSlowIn)
  let dotNow ← dotRadius.get
  let active := if enabled then colors.primary
                else colors.onSurface.withAlpha disabledContentAlpha
  let inactive := if enabled then colors.onSurfaceVariant
                  else colors.onSurface.withAlpha disabledContentAlpha
  let m := modifier
    |>.size 40 40
    |>.semantics (role := some .radioButton) (selected := some selected)
    |>.clickable (do (← clickRef.get)) enabled (source := some source)
    |>.then layer
    |>.drawBehind (drawRadio (if selected then active else inactive) active dotNow)
  Layout m .leaf

end Compose
