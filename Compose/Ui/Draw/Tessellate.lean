import Compose.Ui.Draw.Mesh
import Compose.Ui.Draw.Brush

/-!
# Tessellation (`Compose/Ui/Draw/Tessellate.lean`)

Pure conversion of shapes to anti-aliased triangle `Mesh`es. SDL's 2D renderer
has no anti-aliasing, so every curved/rounded shape is triangulated with a
**1-px feathered outer ring**: the silhouette is duplicated, pushed out 1 px
along the outward normal, and given alpha `0`, so the edge fades from opaque
interior to transparent over one pixel (Compose relies on Skia's analytic AA;
this is our software equivalent).

No SDL, no `IO`: everything here is a total function of geometry to a `Mesh`,
heavily `#guard`-tested. Degenerate inputs (zero size/radius/sweep/width) return
`Mesh.empty` rather than panicking.

Adaptive corner tessellation uses `max 4 ⌈(π/2)·r / 2⌉` segments per quarter
turn, matching the DESIGN note.
-/

namespace Compose.Draw
open Compose

/-- 1-px feather width used for the anti-aliasing ring. -/
private def feather : Float32 := 1.0

/-- π as a `Float32` (Lean's stdlib has no `Float.pi`). -/
private def piF : Float32 := 3.14159265358979323846

/-- Normalize an offset to unit length; the zero vector maps to itself. -/
private def norm (v : Offset) : Offset :=
  let len := (v.x * v.x + v.y * v.y).sqrt
  if len <= 1e-6 then ⟨0, 0⟩ else ⟨v.x / len, v.y / len⟩

/-- Right-hand perpendicular of a direction (`⟨x, y⟩ ↦ ⟨y, -x⟩`). -/
private def perp (d : Offset) : Offset := ⟨d.y, -d.x⟩

/-- Push one triangle's vertex indices (as `Int32`, the mesh's storage form). -/
private def pushTri (is : Array Int32) (a b c : Nat) : Array Int32 :=
  is.push (Int32.ofNat a) |>.push (Int32.ofNat b) |>.push (Int32.ofNat c)

/-- Point on an axis-aligned ellipse centered at `c` with radii `rx`/`ry` at
angle `a` (radians). `cos`/`sin` are evaluated in `Float` then narrowed. -/
private def ellipsePt (c : Offset) (rx ry a : Float32) : Offset :=
  ⟨c.x + rx * (Float.cos a.toFloat).toFloat32, c.y + ry * (Float.sin a.toFloat).toFloat32⟩

/-- Adaptive segment count for a quarter turn of radius `r`:
`max 4 ⌈(π/2)·r / 2⌉`. -/
def cornerSegments (r : Float32) : Nat :=
  max 4 ((piF.toFloat / 2.0 * r.toFloat / 2.0).ceil.toUInt64.toNat)

#guard cornerSegments 0 == 4
#guard cornerSegments 4 == 4          -- ⌈π/2·4/2⌉ = ⌈π⌉ = 4
#guard cornerSegments 100 == 79       -- ⌈π/2·100/2⌉ = ⌈78.5…⌉ = 79

/-! ## Convex-polygon fill with feathered edge -/

/-- Fill a convex polygon (given by its ordered silhouette `pts`) with a 1-px
feathered edge. Triangulated as a fan from the centroid; each edge grows a
feather quad whose outer vertices sit 1 px outside along the outward normal with
alpha `0`. Returns `Mesh.empty` for fewer than three points.

Vertex layout: index `0` is the centroid (opaque), `1 + i` the opaque silhouette
point `i`, `1 + n + i` its feather twin (alpha `0`). Built linearly (FBIP). -/
def fillPolygon (pts : Array Offset) (color : Color) : Mesh := Id.run do
  let n := pts.size
  if n < 3 then return .empty
  -- centroid
  let mut cx : Float32 := 0
  let mut cy : Float32 := 0
  for p in pts do
    cx := cx + p.x; cy := cy + p.y
  let centroid : Offset := ⟨cx / n.toFloat32, cy / n.toFloat32⟩
  let featherColor := color.withAlpha 0
  -- vertices: centroid, then inner ring, then feather ring
  let mut vs : Array DVertex := Array.emptyWithCapacity (2 * n + 1)
  vs := vs.push ⟨centroid, color⟩
  for p in pts do
    vs := vs.push ⟨p, color⟩
  for i in [0:n] do
    let prev := pts[(i + n - 1) % n]!
    let cur := pts[i]!
    let next := pts[(i + 1) % n]!
    -- outward normal: average of the two adjacent edge normals, flipped to
    -- point away from the centroid; fall back to the radial direction.
    let orient (nrm cur : Offset) : Offset :=
      if (Offset.dot nrm (cur - centroid)) < 0 then -nrm else nrm
    let n1 := orient (perp (cur - prev)) cur
    let n2 := orient (perp (next - cur)) cur
    let nrm :=
      let s := norm (n1 + n2)
      if s == (⟨0, 0⟩ : Offset) then norm (cur - centroid) else s
    vs := vs.push ⟨cur + nrm * feather, featherColor⟩
  -- indices
  let mut is : Array Int32 := Array.emptyWithCapacity (9 * n)
  for i in [0:n] do
    let j := (i + 1) % n
    -- interior fan triangle
    is := pushTri is 0 (1 + i) (1 + j)
    -- feather quad (inner i, inner j, outer j, outer i)
    let ii := 1 + i
    let ij := 1 + j
    let oi := 1 + n + i
    let oj := 1 + n + j
    is := pushTri is ii ij oj
    is := pushTri is ii oj oi
  return { vertices := vs, indices := is }

/-! ## Stroke of a silhouette with feathered edges -/

/-- Stroke a silhouette given as `(point, outward unit normal)` samples with the
given `width`, centered on the boundary, feathered 1 px on both sides. `closed`
wraps the last sample back to the first (rings); otherwise the polyline is
stroked with butt caps. Returns `Mesh.empty` for `width ≤ 0` or fewer than two
samples.

Per sample: `inner = p − n·w/2`, `outer = p + n·w/2`, each with an alpha-`0`
feather twin 1 px further out. -/
def strokeSilhouette (samples : Array (Offset × Offset)) (width : Float32)
    (color : Color) (closed : Bool) : Mesh := Id.run do
  let n := samples.size
  if width <= 0 || n < 2 then return .empty
  let w2 := width / 2
  let fc := color.withAlpha 0
  let mut vs : Array DVertex := Array.emptyWithCapacity (4 * n)
  -- rings: inner(0..n), outer(n..2n), innerFeather(2n..3n), outerFeather(3n..4n)
  for (p, nrm) in samples do
    vs := vs.push ⟨p - nrm * w2, color⟩
  for (p, nrm) in samples do
    vs := vs.push ⟨p + nrm * w2, color⟩
  for (p, nrm) in samples do
    vs := vs.push ⟨p - nrm * (w2 + feather), fc⟩
  for (p, nrm) in samples do
    vs := vs.push ⟨p + nrm * (w2 + feather), fc⟩
  let edges := if closed then n else n - 1
  let mut is : Array Int32 := Array.emptyWithCapacity (18 * edges)
  let quad (a b c d : Nat) (acc : Array Int32) : Array Int32 :=
    pushTri (pushTri acc a b c) a c d
  for i in [0:edges] do
    let j := (i + 1) % n
    let inI := i;         let inJ := j
    let outI := n + i;    let outJ := n + j
    let ifI := 2*n + i;   let ifJ := 2*n + j
    let ofI := 3*n + i;   let ofJ := 3*n + j
    is := quad inI inJ outJ outI is           -- solid band
    is := quad inI inJ ifJ ifI is             -- inner feather
    is := quad outI outJ ofJ ofI is           -- outer feather
  return { vertices := vs, indices := is }

/-! ## Silhouette generators -/

/-- The clockwise silhouette of `rr` (already assumed normalized) as
`(point, outward unit normal)` samples. Each rounded corner contributes an arc
of `cornerSegments`-many samples with exact radial normals; a zero-radius corner
contributes its single corner point with the diagonal (mitered) normal. -/
def roundRectSilhouette (rr : RoundRect) : Array (Offset × Offset) := Id.run do
  let r := rr.rect
  let mut out : Array (Offset × Offset) := #[]
  -- (centerx, centery, rx, ry, startAngle, diagonal normal for the zero case)
  let corners : Array (Float32 × Float32 × Float32 × Float32 × Float32 × Offset) := #[
    (r.left + rr.topLeft.x,     r.top + rr.topLeft.y,        rr.topLeft.x,     rr.topLeft.y,     piF,            norm ⟨-1, -1⟩),
    (r.right - rr.topRight.x,   r.top + rr.topRight.y,       rr.topRight.x,    rr.topRight.y,    piF * 1.5,      norm ⟨ 1, -1⟩),
    (r.right - rr.bottomRight.x, r.bottom - rr.bottomRight.y, rr.bottomRight.x, rr.bottomRight.y, 0,             norm ⟨ 1,  1⟩),
    (r.left + rr.bottomLeft.x,  r.bottom - rr.bottomLeft.y,  rr.bottomLeft.x,  rr.bottomLeft.y,  piF * 0.5,      norm ⟨-1,  1⟩)]
  for (cx, cy, rx, ry, a0, diag) in corners do
    if rx <= 1e-4 && ry <= 1e-4 then
      out := out.push (⟨cx, cy⟩, diag)
    else
      let segs := cornerSegments (max rx ry)
      for k in [0:segs + 1] do
        let a := a0 + piF / 2 * (k.toFloat32 / segs.toFloat32)
        let p := ellipsePt ⟨cx, cy⟩ rx ry a
        -- radial outward normal on the ellipse boundary
        let nrm := norm ⟨(Float.cos a.toFloat).toFloat32, (Float.sin a.toFloat).toFloat32⟩
        out := out.push (p, nrm)
  return out

/-- Circle silhouette (`4 · cornerSegments` samples) as `(point, radial normal)`,
starting at the `+x` cardinal point (index `0`) so the four cardinal points land
exactly on multiples of the per-quadrant segment count. -/
def circleSilhouette (center : Offset) (radius : Float32) : Array (Offset × Offset) := Id.run do
  let segs := cornerSegments radius
  let total := 4 * segs
  let mut out : Array (Offset × Offset) := Array.emptyWithCapacity total
  for k in [0:total] do
    let a := 2 * piF * (k.toFloat32 / total.toFloat32)
    let dir : Offset := ⟨(Float.cos a.toFloat).toFloat32, (Float.sin a.toFloat).toFloat32⟩
    out := out.push (center + dir * radius, norm dir)
  return out

/-! ## Public shape tessellators -/

/-- Filled rounded rectangle (radii normalized first). Mirrors
`DrawScope.drawRoundRect` with `Fill` style. A rect with zero radii passes
through as a 4-point polygon fill. Empty rect → `Mesh.empty`. -/
def roundRectFill (rr : RoundRect) (color : Color) : Mesh :=
  if rr.rect.isEmpty then .empty
  else fillPolygon ((roundRectSilhouette rr.normalize).map (·.1)) color

/-- Stroked rounded rectangle, `width` centered on the boundary, feathered both
sides. Mirrors `DrawScope.drawRoundRect` with `Stroke` style. -/
def roundRectStroke (rr : RoundRect) (width : Float32) (color : Color) : Mesh :=
  if rr.rect.isEmpty then .empty
  else strokeSilhouette (roundRectSilhouette rr.normalize) width color (closed := true)

/-- Filled circle. Mirrors `DrawScope.drawCircle` with `Fill` style.
Radius `≤ 0` → `Mesh.empty`. -/
def circleFill (center : Offset) (radius : Float32) (color : Color) : Mesh :=
  if radius <= 0 then .empty
  else fillPolygon ((circleSilhouette center radius).map (·.1)) color

/-- Stroked circle ring, `width` centered on the boundary. Mirrors
`DrawScope.drawCircle` with `Stroke` style. -/
def circleStroke (center : Offset) (radius width : Float32) (color : Color) : Mesh :=
  if radius <= 0 then .empty
  else strokeSilhouette (circleSilhouette center radius) width color (closed := true)

/-- Stroked circular arc from `startRad` sweeping `sweepRad` radians at `radius`
about `center`, butt caps. Used for circular progress indicators (mirrors
`DrawScope.drawArc` with `Stroke` style). Sweep or width `≤ 0` → `Mesh.empty`. -/
def arcStroke (center : Offset) (radius startRad sweepRad width : Float32)
    (color : Color) : Mesh := Id.run do
  if radius <= 0 || width <= 0 || sweepRad.abs <= 1e-6 then return .empty
  -- segment count scales with the swept arc length relative to a quarter turn
  let quarters := (sweepRad.abs / (piF / 2))
  let segs := max 2 ((quarters * (cornerSegments radius).toFloat32).toUInt64.toNat)
  let mut samples : Array (Offset × Offset) := Array.emptyWithCapacity (segs + 1)
  for k in [0:segs + 1] do
    let a := startRad + sweepRad * (k.toFloat32 / segs.toFloat32)
    let dir : Offset := ⟨(Float.cos a.toFloat).toFloat32, (Float.sin a.toFloat).toFloat32⟩
    samples := samples.push (center + dir * radius, norm dir)
  return strokeSilhouette samples width color (closed := false)

/-- A straight line segment from `p0` to `p1` of the given `width`, rendered as a
feathered quad. Mirrors `DrawScope.drawLine`. Zero width or length →
`Mesh.empty`. -/
def line (p0 p1 : Offset) (width : Float32) (color : Color) : Mesh :=
  let d := norm (p1 - p0)
  if width <= 0 || d == (⟨0, 0⟩ : Offset) then .empty
  else
    let nrm := perp d
    strokeSilhouette #[(p0, nrm), (p1, nrm)] width color (closed := false)

/-! ## Circle clipped to a rounded rect (bounded ripple) -/

/-- Signed distance of `p` to the left of the directed edge `a → b`
(> 0 = inside for a clockwise-wound convex clip polygon). -/
private def edgeInside (a b p : Offset) : Float32 :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

/-- Intersection point of segment `s → e` with the infinite line `a → b`. -/
private def edgeIntersect (a b s e : Offset) : Offset :=
  let d1 := edgeInside a b s
  let d2 := edgeInside a b e
  let denom := d1 - d2
  if denom.abs <= 1e-9 then s
  else Offset.lerp s e (d1 / denom)

/-- Sutherland–Hodgman clip of `subject` (a polygon, any winding) against the
convex `clip` polygon (assumed clockwise-wound, as produced by
`roundRectSilhouette`). Returns the clipped polygon's vertices. -/
def clipPolygon (subject clip : Array Offset) : Array Offset := Id.run do
  let m := clip.size
  if m < 3 then return subject
  let mut output := subject
  for i in [0:m] do
    let a := clip[i]!
    let b := clip[(i + 1) % m]!
    let input := output
    output := #[]
    let cnt := input.size
    if cnt == 0 then
      return output
    for k in [0:cnt] do
      let cur := input[k]!
      let prev := input[(k + cnt - 1) % cnt]!
      let curIn := edgeInside a b cur >= 0
      let prevIn := edgeInside a b prev >= 0
      if curIn then
        if !prevIn then
          output := output.push (edgeIntersect a b prev cur)
        output := output.push cur
      else if prevIn then
        output := output.push (edgeIntersect a b prev cur)
  return output

/-- A filled circle clipped to the interior of a rounded rectangle, feathered —
Material's bounded ripple. The circle polygon is Sutherland–Hodgman-clipped
against the (convex) rrect silhouette, then filled. Empty result → `Mesh.empty`. -/
def circleFillClippedToRoundRect (center : Offset) (radius : Float32)
    (rr : RoundRect) (color : Color) : Mesh :=
  if radius <= 0 || rr.rect.isEmpty then .empty
  else
    let circlePts := (circleSilhouette center radius).map (·.1)
    let clipPts := (roundRectSilhouette rr.normalize).map (·.1)
    fillPolygon (clipPolygon circlePts clipPts) color

/-- Clip an arbitrary mesh to a rounded rect. Not yet implemented (documented
future work in DESIGN.md); the ripple path uses `circleFillClippedToRoundRect`
and `DrawScope.clipRoundRect`'s geometric clip instead. Returns `m` unchanged. -/
def clipMeshToRoundRect (m : Mesh) (_rr : RoundRect) : Mesh := m

/-! ## Brush painting -/

/-- Recolor a mesh's vertices from `brush`, evaluated at each vertex's local
position; solid brushes are returned unchanged. Feather vertices (alpha `0`)
stay transparent. -/
def paintMesh (m : Mesh) (brush : Brush) : Mesh :=
  match brush with
  | .solid _ => m
  | .linearGradient .. =>
    { m with vertices := m.vertices.map fun v =>
        let c := brush.colorAt v.pos
        { v with color := if v.color.a == 0 then c.withAlpha 0 else c } }

/-- Build a shape mesh from a tessellator that takes a single fill color: for a
solid brush the color is used directly; for a gradient the shape is tessellated
opaque then repainted per vertex (the tessellator emits a vertex per silhouette
point, so the rasterizer interpolates the gradient across the triangles). -/
def shapeMesh (brush : Brush) (mk : Color → Mesh) : Mesh :=
  match brush with
  | .solid c => mk c
  | .linearGradient .. => paintMesh (mk Color.white) brush

/-! ## Shape specs -/

/-- The complete inputs of one anti-aliased shape draw, in local (wrapper)
coordinates — the shape-level primitive a `DisplayList` carries: the SDL
backend tessellates it (`ShapeSpec.tessellate`), a GPU backend renders it
directly (SDF instancing). Everything the mesh depends on folds in: shape ×
size × density resolve into the `RoundRect`/geometry, a border's `Dp` width ×
density into the pixel `width` — so spec equality is exactly "the cached mesh
is still valid", which also makes it the draw walk's per-node mesh-cache key
(`LayoutNode.cachedMesh`). Compose analog: the `Outline`/`Path` that
`Modifier.background`/`Modifier.border` cache in `drawWithCache` until size or
shape changes. -/
inductive ShapeSpec where
  /-- A filled rounded rect (`roundRectFill`). -/
  | rrFill (rr : RoundRect) (brush : Brush)
  /-- A stroked rounded rect of pixel `width`, centered on the boundary
  (`roundRectStroke`). -/
  | rrStroke (rr : RoundRect) (width : Float32) (brush : Brush)
  /-- A filled circle (`circleFill`). -/
  | circleFill (center : Offset) (radius : Float32) (brush : Brush)
  /-- A filled circle geometrically clipped to a rounded rect — the bounded
  Material ripple (`circleFillClippedToRoundRect`). `rr` is in the same local
  coordinates as `center` (the recorder captures the ambient
  `clipRoundRect` shape). -/
  | circleFillClipped (center : Offset) (radius : Float32) (rr : RoundRect) (brush : Brush)
  /-- A stroked circle of pixel `width` (`circleStroke`). -/
  | circleStroke (center : Offset) (radius width : Float32) (brush : Brush)
  /-- A stroked circular arc, butt caps, radians (`arcStroke`). -/
  | arcStroke (center : Offset) (radius startRad sweepRad width : Float32) (brush : Brush)
  /-- A straight line of pixel `width` (`line`). -/
  | line (p0 p1 : Offset) (width : Float32) (brush : Brush)
  deriving Repr, BEq, Inhabited

/-- Tessellate the mesh a `ShapeSpec` describes (a pure function — the spec
*is* the tessellation's full input). -/
def ShapeSpec.tessellate : ShapeSpec → Mesh
  | .rrFill rr brush => shapeMesh brush (roundRectFill rr)
  | .rrStroke rr width brush => shapeMesh brush (roundRectStroke rr width)
  | .circleFill center radius brush => shapeMesh brush (Compose.Draw.circleFill center radius)
  | .circleFillClipped center radius rr brush =>
    shapeMesh brush (circleFillClippedToRoundRect center radius rr)
  | .circleStroke center radius width brush =>
    shapeMesh brush (Compose.Draw.circleStroke center radius width)
  | .arcStroke center radius startRad sweepRad width brush =>
    shapeMesh brush (Compose.Draw.arcStroke center radius startRad sweepRad width)
  | .line p0 p1 width brush => shapeMesh brush (Compose.Draw.line p0 p1 width)

#guard ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)
        == ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)
#guard ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)
        != ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 41⟩ 8) (.solid .red)  -- size change
#guard ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)
        != ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .blue) -- brush change
#guard ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)
        != ShapeSpec.rrStroke (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) 2 (.solid .red)
#guard (ShapeSpec.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .red)).tessellate
        == roundRectFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red
#guard (ShapeSpec.rrStroke (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) 3 (.solid .blue)).tessellate
        == roundRectStroke (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) 3 .blue
#guard (ShapeSpec.circleFill ⟨50, 50⟩ 20 (.solid .green)).tessellate == circleFill ⟨50, 50⟩ 20 .green
#guard (ShapeSpec.line ⟨0, 0⟩ ⟨10, 10⟩ 2 (.solid .black)).tessellate == line ⟨0, 0⟩ ⟨10, 10⟩ 2 .black
-- Gradient specs tessellate opaque then repaint per vertex.
#guard (ShapeSpec.rrFill (RoundRect.ofRect ⟨0, 0, 10, 10⟩)
          (.linearGradient #[(0, .red), (1, .blue)] ⟨0, 0⟩ ⟨10, 0⟩)).tessellate
        == paintMesh (roundRectFill (RoundRect.ofRect ⟨0, 0, 10, 10⟩) .white)
             (.linearGradient #[(0, .red), (1, .blue)] ⟨0, 0⟩ ⟨10, 0⟩)

/-! ## `#guard` tests -/

/-- Approximate offset equality for float tolerance in compile-time tests. -/
private def approxOff (a b : Offset) (tol : Float32 := 0.05) : Bool :=
  (a.x - b.x).abs <= tol && (a.y - b.y).abs <= tol

-- Well-formedness: all indices in range, triangle-count consistent.
#guard (roundRectFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).indicesInRange
#guard (circleFill ⟨50, 50⟩ 20 .green).indicesInRange
#guard (roundRectStroke (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) 4 .blue).indicesInRange
#guard (circleStroke ⟨50, 50⟩ 20 3 .blue).indicesInRange
#guard (arcStroke ⟨50, 50⟩ 20 0 (piF / 2) 4 .red).indicesInRange
#guard (line ⟨0, 0⟩ ⟨10, 10⟩ 2 .black).indicesInRange
#guard (circleFillClippedToRoundRect ⟨20, 20⟩ 30 (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).indicesInRange

-- A plain zero-radius rect fills as a 4-point polygon: 2·4+1 = 9 verts, 9·4 idx.
#guard (roundRectFill (RoundRect.ofRect ⟨0, 0, 10, 10⟩) .red).vertexCount == 9
#guard (roundRectFill (RoundRect.ofRect ⟨0, 0, 10, 10⟩) .red).triangleCount == 12

-- fillPolygon vertex/index counts for n points: 2n+1 verts, 3n triangles.
#guard (fillPolygon #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] .red).vertexCount == 9
#guard (fillPolygon #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] .red).triangleCount == 12

-- Interior alpha preserved (centroid + inner ring opaque), feather ring alpha 0.
#guard (fillPolygon #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] Color.red).vertices[0]!.color.a == 1.0
#guard (fillPolygon #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] Color.red).vertices[1]!.color.a == 1.0
#guard (fillPolygon #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] Color.red).vertices[5]!.color.a == 0.0

-- Circle cardinal points: index 0 is exactly the +x point (cos 0 = 1, sin 0 = 0).
#guard (circleSilhouette ⟨50, 50⟩ 20)[0]!.1 == (⟨70, 50⟩ : Offset)   -- right cardinal, exact
#guard (circleSilhouette ⟨50, 50⟩ 20)[0]!.2 == (⟨1, 0⟩ : Offset)     -- outward normal +x
-- the four cardinal points are present (right, bottom, left, top) at quadrant starts
#guard
  let s := circleSilhouette ⟨50, 50⟩ 20
  let q := s.size / 4
  approxOff s[0]!.1 ⟨70, 50⟩ && approxOff s[q]!.1 ⟨50, 70⟩ &&
    approxOff s[2*q]!.1 ⟨30, 50⟩ && approxOff s[3*q]!.1 ⟨50, 30⟩

-- roundRect corner extremes: the top-left silhouette starts at the left edge.
#guard
  let s := roundRectSilhouette (RoundRect.circular ⟨0, 0, 40, 40⟩ 8)
  approxOff s[0]!.1 ⟨0, 8⟩            -- left edge, top of the arc

-- Stroke vertex layout: closed ring of n samples → 4n verts, 18n indices.
#guard
  let s := circleSilhouette ⟨0, 0⟩ 10
  let n := s.size
  (circleStroke ⟨0, 0⟩ 10 2 .red).vertexCount == 4 * n

-- Degenerate inputs never panic; they produce the empty mesh.
#guard (roundRectFill (RoundRect.ofRect ⟨0, 0, 0, 0⟩) .red).isEmpty
#guard (circleFill ⟨0, 0⟩ 0 .red).isEmpty
#guard (circleFill ⟨0, 0⟩ (-5) .red).isEmpty
#guard (circleStroke ⟨0, 0⟩ 10 0 .red).isEmpty
#guard (arcStroke ⟨0, 0⟩ 10 0 0 4 .red).isEmpty
#guard (line ⟨5, 5⟩ ⟨5, 5⟩ 2 .red).isEmpty
#guard (line ⟨0, 0⟩ ⟨10, 0⟩ 0 .red).isEmpty

-- Clipping a fully-contained polygon returns it unchanged (all inside).
#guard (clipPolygon #[⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩] #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩]).size == 3
-- Clipping a circle far larger than the rrect yields a bounded (non-empty) fill.
#guard !(circleFillClippedToRoundRect ⟨20, 20⟩ 100 (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).isEmpty
-- Clipping a circle entirely outside the rrect yields an empty polygon.
#guard (circleFillClippedToRoundRect ⟨500, 500⟩ 5 (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).isEmpty

end Compose.Draw
