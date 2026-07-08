import Compose.Ui.Node
import Compose.Ui.Input.HitTest
import Compose.Runtime.Composer
import Compose.Runtime.LaunchedEffect

namespace Compose

/-!
# Layout composable and draw walk (`Compose/Ui/Layout.lean`)

`Layout` is the primitive every container/leaf builds on: it emits a
`LayoutNode` into the composition (via `emitNode`) and reconciles its
modifier chain and measure policy on recomposition, mirroring
`androidx.compose.ui.layout.Layout`.

`LayoutNode.drawTree` is the per-frame draw walk: at each node it executes
the draw modifiers resolved by the last measure (outer to inner —
`background` under `border` under content; `clip`/`alpha` scope everything
inner including children), then draws the children in order (later siblings
on top), translated to their placed positions. This is the one layout module
that runs `DrawM` (and therefore touches the SDL-backed draw scope).
-/

open Draw

/-- Emit a `LayoutNode` measured by `policy`, decorated with `modifier`, with
`content` composing its children. On recomposition the update phase diffs the
chain: a layout-affecting modifier change or policy change invalidates
measurement; a draw-only change just requests a redraw. `policyInputs` gives
the policy an input identity (hash of what it captures) so unchanged policies
skip invalidation; `none` conservatively treats the policy as changed every
update (Compose's capturing-lambda `set(measurePolicy)` behavior). The update
phase also reconciles the chain's `Modifier.pointerInput` coroutines against
the ambient `LocalScheduler` (launch on enter/key change, cancel on leave —
see `LayoutNode.reconcilePointerInputs`). Mirrors
`androidx.compose.ui.layout.Layout`. -/
def Layout (modifier : Modifier) (policy : MeasurePolicy)
    (content : Composable Unit := pure ())
    (policyInputs : Option UInt64 := none) : Composable Unit :=
  emitNode (create := return NodeVal.mk (← LayoutNode.create))
    (update := fun nv => do
      LayoutNode.update nv.get! modifier policy policyInputs
      LayoutNode.reconcilePointerInputs nv.get! (← LocalScheduler.current))
    content

namespace LayoutNode

/-- Translate a rounded rect by `o` (radii unchanged). -/
private def rrTranslate (rr : RoundRect) (o : Offset) : RoundRect :=
  { rr with rect := rr.rect.translate o }

#guard rrTranslate (RoundRect.circular ⟨0, 0, 10, 10⟩ 2) ⟨5, 6⟩
        == RoundRect.circular ⟨5, 6, 15, 16⟩ 2

/-- Shrink a rounded rect by `d` px on all sides, radii clamped at zero — the
centerline of a border stroke drawn just inside the bounds. -/
private def rrInset (rr : RoundRect) (d : Float32) : RoundRect :=
  let f (c : CornerRadius) : CornerRadius := ⟨max 0 (c.x - d), max 0 (c.y - d)⟩
  { rect := rr.rect.inflate (-d)
    topLeft := f rr.topLeft, topRight := f rr.topRight
    bottomRight := f rr.bottomRight, bottomLeft := f rr.bottomLeft }

#guard rrInset (RoundRect.circular ⟨0, 0, 10, 10⟩ 3) 1 == RoundRect.circular ⟨1, 1, 9, 9⟩ 2
#guard rrInset (RoundRect.circular ⟨0, 0, 10, 10⟩ 1) 2 == RoundRect.circular ⟨2, 2, 8, 8⟩ 0

mutual

/-- Draw the subtree rooted at `n` into the ambient `DrawM` context (the
caller is positioned at the node's outer top-left). Clears `needsRedraw`. -/
partial def drawTree (n : LayoutNode) : DrawM Unit := do
  let d ← n.data
  n.modifyData fun x => { x with needsRedraw := false }
  drawResolved n d 0

/-- Execute the resolved draw elements from index `k` inward, then the
children. `clip`/`alpha` elements scope everything inner by wrapping the
continuation. -/
private partial def drawResolved (n : LayoutNode) (d : LayoutNodeData) (k : Nat) :
    DrawM Unit := do
  if hk : k < d.resolvedDraws.size then
    let rd := d.resolvedDraws[k]
    let cont := drawResolved n d (k + 1)
    match d.modifier.elems[rd.elemIdx]? with
    | some (.draw de) =>
      let ctx ← read
      let sz := rd.size.toSize
      let off := rd.offset.toOffset
      match de with
      | .background color .rectangle =>
        match ctx.clipShape with
        | some rr =>
          if rr.rect == Rect.ofOffsetSize off sz then
            -- The `clip(shape).background(color)` idiom: fill the enclosing
            -- clip shape itself so the fill is geometrically clipped
            -- (`rr` is already in this node's coordinates).
            DrawScope.drawRoundRect (.solid color) rr
          else
            -- Partial overlap degrades to the rectangular bounds clip
            -- (DESIGN.md's documented rounded-clip limitation).
            DrawScope.drawRect (.solid color) off sz
        | none =>
          -- Crisp axis-aligned fast path.
          DrawScope.drawRect (.solid color) off sz
        cont
      | .background color shape =>
        DrawScope.translate off <|
          DrawScope.drawRoundRect (.solid color) (shape.toRoundRect sz ctx.density)
        cont
      | .border w color shape =>
        let wpx := ctx.density.dpToPx w
        DrawScope.translate off <|
          DrawScope.drawRoundRect (.solid color)
            (rrInset (shape.toRoundRect sz ctx.density) (wpx / 2)) (.stroke wpx)
        cont
      | .clip .rectangle =>
        DrawScope.clipRect (Rect.ofOffsetSize off sz) cont
      | .clip shape =>
        DrawScope.clipRoundRect (rrTranslate (shape.toRoundRect sz ctx.density) off) cont
      | .alpha a =>
        DrawScope.withAlpha a cont
      | .drawBehind block =>
        DrawScope.translate off block
        cont
    | _ =>
      -- Resolved index no longer points at a draw element (stale between a
      -- draw-only update and the next measure): skip defensively.
      cont
  else
    DrawScope.translate d.contentOffset.toOffset do
      for ch in d.children do
        DrawScope.translate (← ch.data).position.toOffset (drawTree ch)

end

end LayoutNode

end Compose
