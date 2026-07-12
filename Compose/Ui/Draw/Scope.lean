import Compose.Ui.Draw.DisplayList
import Compose.Core.Density

/-!
# Draw scope (`Compose/Ui/Draw/Scope.lean`)

The imperative drawing surface — a *recorder*. Mirrors
`androidx.compose.ui.graphics.drawscope.DrawScope`: a reader over a transform
stack (translation), a clip stack, an alpha multiplier, and the ambient
`Density`. Every draw op resolves that ambient state into a `PrimState` and
appends one backend-neutral primitive to the pass's `DisplayList`
(`Compose/Ui/Draw/DisplayList.lean`); a `RenderBackend` executes the list
afterwards (`SdlBackend.lean` for SDL_Renderer — where the former direct-SDL
emission now lives — or the GPU backend).

Clip rectangles compose by pure intersection, tracked in render-target
coordinates. `clipRoundRect` additionally exposes the rounded shape two ways:
`clipShape` (local coordinates) lets shape-aware draws inside it geometrically
clip at record time (the Material ripple), and `PrimState.rounded`
(render-target coordinates) rides on every recorded primitive so a GPU
backend clips arbitrary content exactly — on the SDL backend arbitrary
content still only gets the rectangular bounds clip (a documented
approximation, per DESIGN.md).
-/

namespace Compose.Draw
open Compose

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
  /-- The display list this pass records into. -/
  sink : IO.Ref (Array Prim)
  /-- Accumulated translation mapping local draw coordinates to render-target
  pixels. -/
  translation : Offset := .zero
  /-- Current clip rectangle in render-target coordinates (`none` = unclipped). -/
  clip : Option Rect := none
  /-- Current rounded clip shape, in local coordinates, exposed by
  `clipRoundRect` for shape-aware geometric clipping at record time (`none` =
  rectangular clip only). -/
  clipShape : Option RoundRect := none
  /-- Current rounded clip shape in render-target coordinates, stamped onto
  every recorded primitive (`PrimState.rounded`) for backends that clip
  exactly. -/
  rounded : Option RoundRect := none
  /-- Accumulated alpha multiplier folded into every draw. -/
  alpha : Float32 := 1.0
  /-- The ambient density for `Dp`/`Sp` resolution by callers. -/
  density : Density := {}
  /-- Size of the region the current block draws into (the decorated wrapper
  for a `Modifier.drawBehind` block, set by the draw walk; `.zero` when the
  caller declared none). Mirrors `DrawScope.size`. -/
  size : Size := .zero

/-- The draw monad: a reader over `DrawContext` in `IO`. Mirrors running inside
Compose's `DrawScope`. -/
abbrev DrawM (α : Type) := ReaderT DrawContext IO α

/-- Debug counter: total shape tessellations since process start, bumped by
every immediate-mode shape draw recorded through `DrawScope` and by every miss
of the draw walk's per-node mesh cache (`LayoutNode.cachedMesh`). Test-visible
so perf tests can assert a static shape tessellates once, not once per rendered
frame. No Compose analog (Skia tessellates internally). -/
initialize tessellationCount : IO.Ref Nat ← IO.mkRef 0

namespace DrawScope

/-- The `PrimState` of the current ambient context. -/
private def stamp (ctx : DrawContext) : PrimState :=
  { origin := ctx.translation, clip := ctx.clip, rounded := ctx.rounded, alpha := ctx.alpha }

/-- Append one primitive built from the current ambient state. -/
private def emit (mk : PrimState → Prim) : DrawM Unit := do
  let ctx ← read
  ctx.sink.modify (·.push (mk (stamp ctx)))

/-- Bump the debug `tessellationCount` (immediate-mode shape draws are
tessellated by the executing backend on every frame they are recorded). -/
private def countTessellation : DrawM Unit :=
  tessellationCount.modify (· + 1)

/-- Record a pre-tessellated `Mesh` (local coordinates); the backend folds in
the ambient translation and alpha at execute time. No-op for an empty mesh.
The draw walk emits cached background/border meshes through `drawShape`
instead, so backends also see the shape-level spec. -/
def drawMesh (m : Mesh) : DrawM Unit := do
  if m.isEmpty then return
  emit (.mesh · m)

/-- Record an anti-aliased shape with an optional pre-tessellated mesh (the
draw walk's per-node cache attaches one; `none` lets the SDL backend
tessellate at execute time). Immediate-mode shape draws below funnel through
here with `cached := none`. -/
def drawShape (spec : ShapeSpec) (cached : Option Mesh := none) : DrawM Unit :=
  emit (.shape · spec cached)

/-- Record a shaped text run with its top-left at `topLeft` (local
coordinates); the run's `PrimState.origin` is the resolved top-left directly.
Called by `TextLayout.draw`. Mirrors `DrawScope.drawText`. -/
def drawText (run : TextRun) (topLeft : Offset) : DrawM Unit := do
  let ctx ← read
  ctx.sink.modify (·.push (.text { stamp ctx with origin := ctx.translation + topLeft } run))

/-! ## Public draw API (mirrors `DrawScope`) -/

/-- Draw an axis-aligned rectangle. A solid `fill` records the crisp
no-tessellation fast path (`Renderer.fillRect` on SDL); gradient fills and
strokes go through the feathered geometry pipeline. Mirrors
`DrawScope.drawRect`. -/
def drawRect (brush : Brush) (topLeft : Offset) (size : Size)
    (style : DrawStyle := .fill) : DrawM Unit := do
  match style, brush with
  | .fill, .solid c =>
    emit (.rect · c topLeft size)
  | .fill, _ =>
    countTessellation
    drawShape (.rrFill (RoundRect.ofRect (Rect.ofOffsetSize topLeft size)) brush)
  | .stroke w, _ =>
    countTessellation
    drawShape (.rrStroke (RoundRect.ofRect (Rect.ofOffsetSize topLeft size)) w brush)

/-- Draw a rounded rectangle (fill or stroke) via the feathered tessellator.
Mirrors `DrawScope.drawRoundRect`. -/
def drawRoundRect (brush : Brush) (rr : RoundRect) (style : DrawStyle := .fill) : DrawM Unit := do
  countTessellation
  match style with
  | .fill => drawShape (.rrFill rr brush)
  | .stroke w => drawShape (.rrStroke rr w brush)

/-- Draw a circle (fill or stroke). A filled circle inside a `clipRoundRect`
geometrically clips to that shape (the bounded Material ripple). Mirrors
`DrawScope.drawCircle`. -/
def drawCircle (brush : Brush) (center : Offset) (radius : Float32)
    (style : DrawStyle := .fill) : DrawM Unit := do
  let ctx ← read
  countTessellation
  match style with
  | .fill =>
    match ctx.clipShape with
    | some rr => drawShape (.circleFillClipped center radius rr brush)
    | none => drawShape (.circleFill center radius brush)
  | .stroke w => drawShape (.circleStroke center radius w brush)

/-- Draw a stroked circular arc (butt caps) — used for circular progress.
`startRad`/`sweepRad` are in radians. Mirrors `DrawScope.drawArc`
(stroke style). -/
def drawArc (brush : Brush) (center : Offset) (radius startRad sweepRad width : Float32) :
    DrawM Unit := do
  countTessellation
  drawShape (.arcStroke center radius startRad sweepRad width brush)

/-- Draw a straight line of the given `width`. Mirrors `DrawScope.drawLine`. -/
def drawLine (brush : Brush) (p0 p1 : Offset) (width : Float32) : DrawM Unit := do
  countTessellation
  drawShape (.line p0 p1 width brush)

/-! ## Scoping combinators -/

/-- Restrict drawing to `r` (intersected with any enclosing clip), in local
coordinates. Pure state — the resolved clip is stamped on each recorded
primitive. Mirrors `DrawScope.clipRect`. -/
def clipRect (r : Rect) (body : DrawM α) : DrawM α := do
  let ctx ← read
  let target := r.translate ctx.translation
  let newClip := match ctx.clip with
    | none => target
    | some c => Rect.intersect c target
  withReader (fun c => { c with clip := some newClip }) body

/-- Clip to a rounded rectangle. Sets the rectangular bounds clip AND exposes
`rr` so shape-aware draws inside geometrically clip to it (plus the
render-target-coordinate `PrimState.rounded` for backends that clip all
content exactly); on the SDL backend arbitrary content degrades to the
rectangular bounds clip (documented DESIGN.md limitation). Mirrors
`DrawScope.clipRoundRect`. -/
def clipRoundRect (rr : RoundRect) (body : DrawM α) : DrawM α := do
  let ctx ← read
  clipRect rr.rect <| withReader
    (fun c => { c with clipShape := some rr, rounded := some (rr.translate ctx.translation) })
    body

/-- Translate the coordinate system by `o` for the duration of `body`. Mirrors
`DrawScope.translate`. -/
def translate (o : Offset) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with translation := c.translation + o }) body

/-- Multiply the layer alpha by `a` for the duration of `body` (folded into
every draw's output alpha). Mirrors `DrawScope.alpha` / a graphics-layer alpha. -/
def withAlpha (a : Float32) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with alpha := c.alpha * a }) body

/-- Record `body` as an offscreen layer composited once at alpha `a` — real
group opacity, no double-blending where the content overlaps itself (the GPU
backend renders the content to a texture; the SDL backend flattens by folding
`a` into the content, today's documented approximation). `bounds` is the
composite region in local coordinates: content is composited within it (plus
a 1 px AA margin), a documented deviation from Compose's unclipped
`graphicsLayer`. `a ≥ 1` records no layer. The layer's own `a` is *not*
folded into the recorded content — executors apply it at composite time (the
ambient alpha stays folded into content as usual, so a layer primitive's
`PrimState.alpha` is ignored by executors). Backs `Modifier.alpha`; mirrors
`graphicsLayer { alpha = a }`. -/
def withLayer (bounds : Rect) (a : Float32) (body : DrawM α) : DrawM α := do
  if a ≥ 1.0 then
    body
  else
    let ctx ← read
    let sub ← IO.mkRef #[]
    let r ← withReader (fun c => { c with sink := sub }) body
    ctx.sink.modify
      (·.push (.layer (stamp ctx) (bounds.translate ctx.translation) a (← sub.get)))
    return r

/-- Declare the size of the region `body` draws into (readable via
`DrawScope.size`); the draw walk wraps `Modifier.drawBehind` blocks with the
decorated wrapper's size. Mirrors `DrawScope.size` being part of the receiver. -/
def withSize (s : Size) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with size := s }) body

/-- Size of the region the current block draws into (see
`DrawContext.size`). Mirrors `DrawScope.size`. -/
def size : DrawM Size := return (← read).size

/-! ## Entry point -/

/-- Record `body` into a fresh display list with a clean
transform/clip/alpha state at the given `density` (no backend touched). -/
def record (density : Density := {}) (body : DrawM α) : IO (DisplayList × α) := do
  let sink ← IO.mkRef #[]
  let a ← body.run { sink, density }
  return (← sink.get, a)

end DrawScope

end Compose.Draw
