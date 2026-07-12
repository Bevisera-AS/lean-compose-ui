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

/-- Fill vs. stroke for `drawPath`. Unlike the closed-shape `DrawStyle`, a path
stroke carries the full `Stroke` description (caps, joins, miter limit,
dashing): `.stroke { width := 3, cap := .round }`. -/
inductive PathStyle where
  /-- Fill the path's interior under its fill rule. -/
  | fill
  /-- Stroke the path with the given `Stroke`. -/
  | stroke (s : Stroke)
  deriving Repr, BEq, Inhabited

/-- The composite-time properties of a graphics layer, mirroring the mutable
receiver of Compose's `Modifier.graphicsLayer { ... }`: rotation/scale/
translation about a fractional pivot, plus the group alpha. Resolved to an
`Affine` (or nothing, when identity) by `toAffine` at record time. -/
structure GraphicsLayerScope where
  /-- Group alpha applied once at composite. Mirrors `alpha`. -/
  alpha : Float32 := 1
  /-- Rotation about the pivot, degrees clockwise. Mirrors `rotationZ`. -/
  rotationZ : Float32 := 0
  /-- Scale about the pivot. Mirrors `scaleX`/`scaleY`. -/
  scaleX : Float32 := 1
  scaleY : Float32 := 1
  /-- Post-transform displacement in pixels. Mirrors
  `translationX`/`translationY`. -/
  translationX : Float32 := 0
  translationY : Float32 := 0
  /-- Pivot as a fraction of the layer bounds (`⟨0.5, 0.5⟩` = center).
  Mirrors `TransformOrigin`. -/
  transformOrigin : Offset := ⟨0.5, 0.5⟩
  deriving Repr, BEq, Inhabited

namespace GraphicsLayerScope

/-- Resolve to the composite transform about `bounds`'s pivot —
`T(pivot + translation) ∘ R ∘ S ∘ T(−pivot)` — or `none` when the transform
part is identity (alpha is not consulted; pure-alpha layers stay
transform-free). -/
def toAffine (g : GraphicsLayerScope) (bounds : Rect) : Option Affine :=
  if g.rotationZ == 0 && g.scaleX == 1 && g.scaleY == 1
      && g.translationX == 0 && g.translationY == 0 then
    none
  else
    let pivot : Offset := ⟨bounds.left + g.transformOrigin.x * bounds.width,
                           bounds.top + g.transformOrigin.y * bounds.height⟩
    let rad := g.rotationZ * ((3.14159265358979323846 : Float).toFloat32 / 180)
    some ((Affine.translation (pivot + ⟨g.translationX, g.translationY⟩)).comp
      ((Affine.rotation rad).comp
        ((Affine.scaling g.scaleX g.scaleY).comp
          (Affine.translation (-pivot)))))

-- identity settings record no transform; alpha alone doesn't either
#guard ({} : GraphicsLayerScope).toAffine ⟨0, 0, 10, 10⟩ == none
#guard ({ alpha := 0.5 } : GraphicsLayerScope).toAffine ⟨0, 0, 10, 10⟩ == none
-- pure translation
#guard ({ translationX := 3, translationY := -2 } : GraphicsLayerScope).toAffine
        ⟨0, 0, 10, 10⟩ == some (.translation ⟨3, -2⟩)
-- 2× scale about the center of (0,0,10,10): (0,0) ↦ (-5,-5)
#guard ((({ scaleX := 2, scaleY := 2 } : GraphicsLayerScope).toAffine
        ⟨0, 0, 10, 10⟩).getD .identity).mapOffset ⟨0, 0⟩ == ⟨-5, -5⟩
-- the pivot is a fixed point of rotation + scale
#guard (((({ rotationZ := 90, scaleX := 3, scaleY := 2 } : GraphicsLayerScope).toAffine
        ⟨10, 10, 30, 50⟩).getD .identity).mapOffset ⟨20, 30⟩).distance ⟨20, 30⟩ <= 1e-4
-- 90° about the center of (0,0,40,40): (0,0) ↦ (40,0)
#guard (((({ rotationZ := 90 } : GraphicsLayerScope).toAffine
        ⟨0, 0, 40, 40⟩).getD .identity).mapOffset ⟨0, 0⟩).distance ⟨40, 0⟩ <= 1e-3

end GraphicsLayerScope

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
  /-- Current path clip in **render-target** coordinates (`none` = no path
  clip), set by `clipPath`: `drawPath` fills translate it back into their
  local frame and record `ShapeSpec.pathFillClipped` (exact on both
  backends); all other content degrades to the rectangular bounds clip. -/
  clipPathShape : Option Path := none
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

/-- Draw an arbitrary vector `path` — both styles rasterize through the exact
band-sweep tessellation on both backends. A fill inside `clipPath` records
`ShapeSpec.pathFillClipped` (the clip translated into this draw's local
frame); a stroke carries its full `Stroke` (caps/joins/miter/dash) and, like
all non-path-fill content, degrades to the clip's bounds rectangle. Mirrors
`DrawScope.drawPath`. -/
def drawPath (brush : Brush) (path : Path) (style : PathStyle := .fill) : DrawM Unit := do
  let ctx ← read
  countTessellation
  match style with
  | .fill =>
    match ctx.clipPathShape with
    | some clip => drawShape (.pathFillClipped path (clip.translate (-ctx.translation)) brush)
    | none => drawShape (.pathFill path brush)
  | .stroke s => drawShape (.pathStroke path s brush)

/-- Draw (a `src` portion of) an image stretched onto the `dst` rectangle
(local coordinates; `src` defaults to the whole image). The ambient alpha
folds into the draw at execute time. Non-linear scaling picks between
`.linear` filtering (the default) and `.nearest` (crisp pixel art). Mirrors
`DrawScope.drawImage`. -/
def drawImage (img : ImageBitmap) (dst : Rect) (src : Option Rect := none)
    (sampling : Sampling := .linear) : DrawM Unit :=
  emit (.image · img src dst sampling)

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

/-- Clip to an arbitrary vector path. Sets the rectangular bounds clip to the
path's bounds AND exposes the path (render-target coordinates) so `drawPath`
fills inside clip to it *exactly* on both backends
(`ShapeSpec.pathFillClipped` — one band sweep, two winding accumulators); all
other content degrades to the bounds clip (documented DESIGN.md limitation,
like the SDL rounded-clip story). A nested `clipPath` replaces the ambient
path (only the innermost is exact); bounds rectangles still intersect.
Mirrors `DrawScope.clipPath`. -/
def clipPath (path : Path) (body : DrawM α) : DrawM α := do
  let ctx ← read
  clipRect path.bounds <| withReader
    (fun c => { c with clipPathShape := some (path.translate ctx.translation) })
    body

/-- Translate the coordinate system by `o` for the duration of `body`. Mirrors
`DrawScope.translate`. -/
def translate (o : Offset) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with translation := c.translation + o }) body

/-- Multiply the layer alpha by `a` for the duration of `body` (folded into
every draw's output alpha). Mirrors `DrawScope.alpha` / a graphics-layer alpha. -/
def withAlpha (a : Float32) (body : DrawM α) : DrawM α :=
  withReader (fun c => { c with alpha := c.alpha * a }) body

/-- Record `body` as an offscreen graphics layer composited once with `g`'s
alpha and transform — real group opacity (no double-blending where the
content overlaps itself) and layer-boundary rotate/scale/translate: content
records untransformed, executors render it to a texture and map only the
composite. `bounds` is the *content* region in local coordinates: content is
composited within it (plus a margin — 1 px AA, or the `effect`'s spread), a
documented deviation from Compose's unclipped `graphicsLayer`. Identity
transform at alpha `≥ 1` with no effect records no layer (`effect` normalizes
first: blur σ ≤ 0 is no effect, σ caps at 16). The layer's own
alpha/transform/effect are *not* folded into the recorded content — executors
apply them at composite time (the ambient alpha stays folded into content as
usual, so a layer primitive's `PrimState.alpha` is ignored by executors).
Backs `Modifier.graphicsLayer` and `Modifier.blur`; mirrors
`graphicsLayer { ... }`. -/
def withGraphicsLayer (bounds : Rect) (g : GraphicsLayerScope) (body : DrawM α)
    (effect : LayerEffect := .none) : DrawM α := do
  let ctx ← read
  let target := bounds.translate ctx.translation
  let transform := g.toAffine target
  let effect := effect.normalize
  if transform.isNone && g.alpha ≥ 1.0 && effect == .none then
    body
  else
    let sub ← IO.mkRef #[]
    -- Under a transform, enclosing clips must scissor the *composite* (they
    -- are target-coordinate regions — they apply where pixels land), not
    -- crop the content pre-transform: strip the ambient clip state from the
    -- content (the layer prim itself keeps it via `stamp`), so only clips
    -- established inside the layer bake into the texture and rotate with it.
    let r ← withReader (fun c =>
      if transform.isSome then
        { c with sink := sub
                 clip := none, clipShape := none, clipPathShape := none, rounded := none }
      else
        { c with sink := sub }) body
    ctx.sink.modify
      (·.push (.layer (stamp ctx) target { alpha := g.alpha, transform, effect } (← sub.get)))
    return r

/-- Record `body` as an offscreen layer composited once at alpha `a` (see
`withGraphicsLayer` — this is its transform-free case). `a ≥ 1` with no
`effect` records no layer. Backs `Modifier.alpha`; mirrors
`graphicsLayer { alpha = a }`. -/
def withLayer (bounds : Rect) (a : Float32) (body : DrawM α)
    (effect : LayerEffect := .none) : DrawM α :=
  withGraphicsLayer bounds { alpha := a } body (effect := effect)

/-- Record `body` as an offscreen layer Gaussian-blurred with standard
deviation `sigma` (device px, capped at 16; `σ ≤ 0` records no layer) before
compositing — even at full alpha. GPU-only: the SDL backend renders the
content unblurred (documented). `bounds` is the content region; the blurred
composite spreads `3σ + 1` px past it. Backs `Modifier.blur`. -/
def withBlur (bounds : Rect) (sigma : Float32) (body : DrawM α) : DrawM α :=
  withGraphicsLayer bounds {} body (effect := .blur sigma)

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
