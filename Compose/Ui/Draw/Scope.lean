import Compose.Ui.Draw.Tessellate
import Compose.Ui.Draw.Brush
import Compose.Core.Density
import Sdl

/-!
# Draw scope (`Compose/Ui/Draw/Scope.lean`)

The imperative drawing surface over SDL — the one draw module that imports
`Sdl`. Mirrors `androidx.compose.ui.graphics.drawscope.DrawScope`: a reader over
the renderer plus a transform stack (translation), a clip-rect stack, an alpha
multiplier, and the ambient `Density`.

Anti-aliased shapes come from the pure tessellator (`Tessellate.lean`) as a
`Mesh`, converted to `Sdl.Vertex` here (translation and alpha folded in at
conversion time). Axis-aligned solid rectangles take the crisp
`Renderer.fillRect` fast path instead of tessellation.

Clip rectangles compose by intersection onto SDL's single render clip rect
(saved and restored around each `clipRect` body); the clip is tracked in
render-target coordinates. `clipRoundRect` additionally exposes the rounded
shape so shape-aware draws inside it (the Material ripple) can geometrically
clip — arbitrary content still only gets the rectangular bounds clip (a
documented approximation, per DESIGN.md).
-/

namespace Compose.Draw
open Compose Sdl

/-- Fill vs. stroke, mirroring `androidx.compose.ui.graphics.drawscope.DrawStyle`
(`Fill` / `Stroke`). Stroke width is in pixels, centered on the boundary. -/
inductive DrawStyle where
  /-- Fill the shape's interior. Mirrors `DrawStyle.Fill`. -/
  | fill
  /-- Stroke the shape's outline with the given pixel `width`. Mirrors
  `DrawStyle.Stroke`. -/
  | stroke (width : Float32)
  deriving Repr, BEq, Inhabited

/-- The ambient drawing state threaded through a draw pass. Mirrors the receiver
state of Compose's `DrawScope` (transform + clip + layer alpha + density). -/
structure DrawContext where
  /-- The SDL renderer all drawing targets. -/
  renderer : Renderer
  /-- Accumulated translation mapping local draw coordinates to render-target
  pixels. -/
  translation : Offset := .zero
  /-- Current clip rectangle in render-target coordinates (`none` = unclipped). -/
  clip : Option Rect := none
  /-- Current rounded clip shape, in local coordinates, exposed by
  `clipRoundRect` for shape-aware geometric clipping (`none` = rectangular clip
  only). -/
  clipShape : Option RoundRect := none
  /-- Accumulated alpha multiplier folded into every draw. -/
  alpha : Float32 := 1.0
  /-- The ambient density for `Dp`/`Sp` resolution by callers. -/
  density : Density := {}

/-- The draw monad: a reader over `DrawContext` in `IO`. Mirrors running inside
Compose's `DrawScope`. -/
abbrev DrawM (α : Type) := ReaderT DrawContext IO α

namespace DrawScope

/-! ## Coordinate / mesh conversion helpers -/

/-- Convert a float `Rect` to an integer `Sdl.Rect`, expanding to whole pixels
(floor the min corner, ceil the max corner) so the clip fully covers the region.
Width/height are clamped non-negative. -/
private def toSdlRect (r : Rect) : Sdl.Rect :=
  let l := r.left.floor.toInt32
  let t := r.top.floor.toInt32
  let rt := r.right.ceil.toInt32
  let bt := r.bottom.ceil.toInt32
  ⟨l, t, max 0 (rt - l), max 0 (bt - t)⟩

/-- Convert a `Mesh` (local coordinates) to SDL geometry, folding in the ambient
`translation` and `alpha`. Feather vertices keep alpha `0` after scaling. -/
private def meshToGeometry (m : Mesh) (translation : Offset) (alpha : Float32) :
    Array Sdl.Vertex × Array Int32 :=
  let verts := m.vertices.map fun v =>
    ({ position := ⟨v.pos.x + translation.x, v.pos.y + translation.y⟩
       color := ⟨v.color.r, v.color.g, v.color.b, v.color.a * alpha⟩
       texCoord := ⟨0, 0⟩ } : Sdl.Vertex)
  let idx := m.indices.map (Int32.ofNat ·)
  (verts, idx)

/-- Recolor a mesh's vertices from `brush`, evaluated at each vertex's local
position; solid brushes are returned unchanged. Feather vertices (alpha `0`)
stay transparent. -/
private def paintMesh (m : Mesh) (brush : Brush) : Mesh :=
  match brush with
  | .solid _ => m
  | .linearGradient .. =>
    { m with vertices := m.vertices.map fun v =>
        let c := brush.colorAt v.pos
        { v with color := if v.color.a == 0 then c.withAlpha 0 else c } }

/-- Build a shape mesh from a tessellator that takes a single fill color: for a
solid brush the color is used directly; for a gradient the shape is tessellated
opaque then repainted per vertex. -/
private def shapeMesh (brush : Brush) (mk : Color → Mesh) : Mesh :=
  match brush with
  | .solid c => mk c
  | .linearGradient .. => paintMesh (mk Color.white) brush

/-- Emit a mesh through `Renderer.geometry` with alpha blending. No-op for an
empty mesh. -/
private def drawMesh (m : Mesh) : DrawM Unit := do
  let ctx ← read
  if m.isEmpty then return
  let (verts, idx) := meshToGeometry m ctx.translation ctx.alpha
  ctx.renderer.setDrawBlendMode .blend
  ctx.renderer.geometry none verts idx

/-! ## Public draw API (mirrors `DrawScope`) -/

/-- Draw an axis-aligned rectangle. A solid `fill` uses the crisp
`Renderer.fillRect` fast path (no tessellation); gradient fills and strokes go
through the feathered geometry pipeline. Mirrors `DrawScope.drawRect`. -/
def drawRect (brush : Brush) (topLeft : Offset) (size : Size)
    (style : DrawStyle := .fill) : DrawM Unit := do
  let ctx ← read
  match style, brush with
  | .fill, .solid c =>
    let col := c.withAlpha (c.a * ctx.alpha)
    let (r, g, b, a) := col.toBytes
    let tl := topLeft + ctx.translation
    ctx.renderer.setDrawBlendMode .blend
    ctx.renderer.setDrawColor r g b a
    ctx.renderer.fillRect (some ⟨tl.x, tl.y, size.width, size.height⟩)
  | .fill, _ =>
    drawMesh (shapeMesh brush (fun c => roundRectFill (RoundRect.ofRect (Rect.ofOffsetSize topLeft size)) c))
  | .stroke w, _ =>
    drawMesh (shapeMesh brush (fun c => roundRectStroke (RoundRect.ofRect (Rect.ofOffsetSize topLeft size)) w c))

/-- Draw a rounded rectangle (fill or stroke) via the feathered tessellator.
Mirrors `DrawScope.drawRoundRect`. -/
def drawRoundRect (brush : Brush) (rr : RoundRect) (style : DrawStyle := .fill) : DrawM Unit :=
  match style with
  | .fill => drawMesh (shapeMesh brush (fun c => roundRectFill rr c))
  | .stroke w => drawMesh (shapeMesh brush (fun c => roundRectStroke rr w c))

/-- Draw a circle (fill or stroke). A filled circle inside a `clipRoundRect`
geometrically clips to that shape (the bounded Material ripple). Mirrors
`DrawScope.drawCircle`. -/
def drawCircle (brush : Brush) (center : Offset) (radius : Float32)
    (style : DrawStyle := .fill) : DrawM Unit := do
  let ctx ← read
  match style with
  | .fill =>
    match ctx.clipShape with
    | some rr => drawMesh (shapeMesh brush (fun c => circleFillClippedToRoundRect center radius rr c))
    | none => drawMesh (shapeMesh brush (fun c => circleFill center radius c))
  | .stroke w => drawMesh (shapeMesh brush (fun c => circleStroke center radius w c))

/-- Draw a stroked circular arc (butt caps) — used for circular progress.
`startRad`/`sweepRad` are in radians. Mirrors `DrawScope.drawArc`
(stroke style). -/
def drawArc (brush : Brush) (center : Offset) (radius startRad sweepRad width : Float32) :
    DrawM Unit :=
  drawMesh (shapeMesh brush (fun c => arcStroke center radius startRad sweepRad width c))

/-- Draw a straight line of the given `width`. Mirrors `DrawScope.drawLine`. -/
def drawLine (brush : Brush) (p0 p1 : Offset) (width : Float32) : DrawM Unit :=
  drawMesh (shapeMesh brush (fun c => line p0 p1 width c))

/-! ## Scoping combinators -/

/-- Restrict drawing to `r` (intersected with any enclosing clip), in local
coordinates. Composes onto SDL's single clip rect and restores it afterwards.
Mirrors `DrawScope.clipRect`. -/
def clipRect (r : Rect) (body : DrawM α) : DrawM α := do
  let ctx ← read
  let target := r.translate ctx.translation
  let newClip := match ctx.clip with
    | none => target
    | some c => Rect.intersect c target
  let restore : IO Unit := match ctx.clip with
    | none => ctx.renderer.setClipRect none
    | some c => ctx.renderer.setClipRect (some (toSdlRect c))
  ctx.renderer.setClipRect (some (toSdlRect newClip))
  tryFinally
    (withReader (fun c => { c with clip := some newClip }) body)
    restore

/-- Clip to a rounded rectangle. Sets the rectangular bounds clip AND exposes
`rr` so shape-aware draws inside geometrically clip to it; arbitrary content
degrades to the rectangular bounds clip (documented DESIGN.md limitation).
Mirrors `DrawScope.clipRoundRect`. -/
def clipRoundRect (rr : RoundRect) (body : DrawM α) : DrawM α :=
  clipRect rr.rect (withReader (fun c => { c with clipShape := some rr }) body)

/-- Translate the coordinate system by `o` for the duration of `body`. Mirrors
`DrawScope.translate`. -/
def translate (o : Offset) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with translation := c.translation + o }) body

/-- Multiply the layer alpha by `a` for the duration of `body` (folded into
every draw's output alpha). Mirrors `DrawScope.alpha` / a graphics-layer alpha. -/
def withAlpha (a : Float32) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with alpha := c.alpha * a }) body

/-! ## Entry point -/

/-- Run a draw block against `renderer` with a fresh transform/clip/alpha state
and the given `density`. -/
def run (renderer : Renderer) (density : Density := {}) (body : DrawM α) : IO α :=
  body.run { renderer, density }

end DrawScope

end Compose.Draw
