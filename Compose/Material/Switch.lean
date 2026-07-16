module

public import Compose.Material.StateLayer
public meta import Compose.Material.StateLayer
public import Compose.Ui.Layout
public meta import Compose.Ui.Layout

public section

namespace Compose

open Draw

/-!
# Switch (`Compose/Material/Switch.lean`)

The Material3 switch: a 52 × 32 dp full-round track whose color animates
`surfaceVariant` ↔ `primary`, with a thumb sliding between the ends on an
`animateDpAsState` spring — and, per M3, growing from 16 dp (unchecked) to
24 dp (checked) diameter. The unchecked track wears a 2 dp `outline` border
that fades out as it checks. A hover/focus state-layer halo (20 dp radius)
follows the thumb. Toggle by click or Enter/Space when focused
(drag-to-toggle is a documented M9 cut). Disabled uses the Material3
12 % / 38 % alphas. Mirrors `androidx.compose.material3.Switch`.
-/

/-- Draw the track, border, thumb, and interaction halo. `thumbX` is the
thumb-center x in dp from the track's left edge; `fraction` the 0→1 checked
progress driving the border fade. -/
private def drawSwitch (track borderColor thumb halo : Color)
    (thumbX thumbRadius : Dp) (fraction haloAlpha : Float32) : DrawM Unit := do
  let ctx ← read
  let sz ← DrawScope.size
  if sz.isEmpty then return
  let px (d : Dp) : Float32 := ctx.density.dpToPx d
  let w := px 52
  let h := px 32
  let origin : Offset := ⟨(sz.width - w) / 2, (sz.height - h) / 2⟩
  let rect : Rect := ⟨origin.x, origin.y, origin.x + w, origin.y + h⟩
  DrawScope.drawRoundRect (.solid track) (RoundRect.circular rect (h / 2))
  let bw := px 2
  let borderAlpha := borderColor.a * (1 - fraction)
  if borderAlpha > 0.005 then
    DrawScope.drawRoundRect (.solid (borderColor.withAlpha borderAlpha))
      (RoundRect.circular (rect.inflate (-bw / 2)) (h / 2 - bw / 2)) (.stroke bw)
  let center : Offset := ⟨origin.x + px thumbX, origin.y + h / 2⟩
  if haloAlpha > 0.001 then
    DrawScope.drawCircle (.solid (halo.withAlpha haloAlpha)) center (px 20)
  DrawScope.drawCircle (.solid thumb) center (px thumbRadius)

/-- A Material switch (see the module docstring). `onCheckedChange` receives
the *new* value. Mirrors `androidx.compose.material3.Switch`. -/
composable def Switch (checked : Bool) (onCheckedChange : Bool → IO Unit)
    (modifier : Modifier := {}) (enabled : Bool := true) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let source ← rememberInteractionSource
  let latest ← rememberUpdatedRef (checked, onCheckedChange)
  let values ← rememberStateLayerValues source
  -- Thumb slides 16 dp ↔ 36 dp (center x) and grows 8 dp ↔ 12 dp (radius),
  -- both on the default spring.
  let thumbX ← animateDpAsState (if checked then 36 else 16)
  let thumbR ← animateDpAsState (if checked then 12 else 8)
  let fraction ← animateFloatAsState (if checked then 1.0 else 0.0)
    (.tween 150 0 .fastOutSlowIn)
  let trackTarget :=
    if enabled then (if checked then colors.primary else colors.surfaceVariant)
    else if checked then colors.onSurface.withAlpha disabledContainerAlpha
    else colors.surfaceVariant.withAlpha disabledContainerAlpha
  let track ← animateColorAsState trackTarget (.tween 150 0 .fastOutSlowIn)
  let trackNow ← track.get
  let thumbXNow ← thumbX.get
  let thumbRNow ← thumbR.get
  let fractionNow ← fraction.get
  let thumbColor :=
    if enabled then (if checked then colors.onPrimary else colors.outline)
    else colors.onSurface.withAlpha disabledContentAlpha
  let borderColor := if enabled then colors.outline else Color.transparent
  let haloAlpha := if enabled then values.layerAlpha else 0
  let m := modifier
    |>.size 52 40
    |>.semantics (role := some .switch) (toggled := some checked)
    |>.clickable (do let (c, f) ← latest.get; f !c) enabled (source := some source)
    |>.drawBehind (drawSwitch trackNow borderColor thumbColor colors.onSurface
        thumbXNow thumbRNow fractionNow haloAlpha)
  Layout m .leaf

end Compose

end
