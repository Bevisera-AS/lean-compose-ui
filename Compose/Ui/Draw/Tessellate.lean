module

public import Compose.Ui.Draw.Mesh
public meta import Compose.Ui.Draw.Mesh
public import Compose.Ui.Draw.Brush
public meta import Compose.Ui.Draw.Brush
public import Compose.Ui.Draw.PathStroke
public meta import Compose.Ui.Draw.PathStroke
public import Compose.Ui.Draw.Gpu.Sdf
public meta import Compose.Ui.Draw.Gpu.Sdf

public section

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

/-- Corner curvature of a rounded rect's fill or stroke. `.circular` is the
classic quarter-circle arc; `.continuous` is the Apple-style **squircle** —
the superellipse `|x/r|⁴ + |y/r|⁴ = 1` in the corner box, whose curvature
vanishes where it meets the straight edges (a G² join, no visible curvature
kink). Threaded `Shape → ShapeSpec → QuadInstance`; both backends draw the
same curve — this tessellator samples it parametrically, the GPU quad
shader evaluates its SDF (`Gpu.Sdf.squircleSdf`). Ambient rounded *clips*,
backdrop-frost masks, and the analytic shadow stay circular-cornered
(documented approximation, DESIGN.md — the styles differ only in a corner
sliver ≤ 0.2 r deep). -/
inductive CornerStyle where
  | circular
  | continuous
  deriving Repr, BEq, Inhabited

/-- Point on the corner superellipse `|dx/rx|⁴ + |dy/ry|⁴ = 1` at parameter
angle `a` — the squircle twin of `ellipsePt`, via the standard superellipse
parametrization `d = (±rx·|cos a|^½, ±ry·|sin a|^½)`; it meets the same
quadrant-boundary endpoints as the circular arc. -/
private def squirclePt (c : Offset) (rx ry a : Float32) : Offset :=
  let ca := Float.cos a.toFloat
  let sa := Float.sin a.toFloat
  let px := (Float.sqrt ca.abs).toFloat32 * (if ca < 0 then -1 else 1)
  let py := (Float.sqrt sa.abs).toFloat32 * (if sa < 0 then -1 else 1)
  ⟨c.x + rx * px, c.y + ry * py⟩

/-- Outward unit normal of the corner superellipse at displacement `d` from
the corner center: `∇(|dx/rx|⁴ + |dy/ry|⁴) ∝ (dx³/rx⁴, dy³/ry⁴)`. At the
quadrant boundaries one component vanishes, so the normal degenerates to
the adjacent edge's axis normal — the smooth join. -/
private def squircleNormal (d : Offset) (rx ry : Float32) : Offset :=
  norm ⟨d.x * d.x * d.x / (rx * rx * rx * rx),
        d.y * d.y * d.y / (ry * ry * ry * ry)⟩

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

/-- Stroke a silhouette given as `(point, outward offset direction)` samples
with the given `width`, centered on the boundary, feathered 1 px on both
sides. Offset directions are unit normals along smooth boundaries; a sharp
corner passes a miter-scaled diagonal (`roundRectSilhouette`'s `⟨±1, ±1⟩`) so
its single sample lands on both adjacent edges' offset lines. `closed` wraps
the last sample back to the first (rings); otherwise the polyline is stroked
with butt caps. Returns `Mesh.empty` for `width ≤ 0` or fewer than two
samples.

Per sample: `inner = p − n·w/2`, `outer = p + n·w/2`, each with an alpha-`0`
feather twin 1 px further out. Open strokes also feather their butt ends: each
end cross-section grows a 1-px apron along the outward tangent (plus two
corner wedges tying it to the side aprons), so arc/line ends anti-alias like
the sides. -/
def strokeSilhouette (samples : Array (Offset × Offset)) (width : Float32)
    (color : Color) (closed : Bool) : Mesh := Id.run do
  let n := samples.size
  if width <= 0 || n < 2 then return .empty
  let w2 := width / 2
  let fc := color.withAlpha 0
  let mut vs : Array DVertex := Array.emptyWithCapacity (4 * n + 4)
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
  let mut is : Array Int32 := Array.emptyWithCapacity (18 * edges + 24)
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
  if !closed then
    -- butt-end feather: an apron off each end cross-section pushed 1 px along
    -- the outward tangent, plus corner wedges joining the side aprons.
    for (i, adj) in #[(0, 1), (n - 1, n - 2)] do
      let e := norm (samples[i]!.1 - samples[adj]!.1)
      if e != (⟨0, 0⟩ : Offset) then
        let base := vs.size
        vs := vs.push ⟨vs[i]!.pos + e * feather, fc⟩         -- inner end twin
        vs := vs.push ⟨vs[n + i]!.pos + e * feather, fc⟩     -- outer end twin
        is := quad i (n + i) (base + 1) base is              -- end apron
        is := pushTri is i base (2*n + i)                    -- inner corner
        is := pushTri is (n + i) (base + 1) (3*n + i)        -- outer corner
  return { vertices := vs, indices := is }

/-! ## Silhouette generators -/

/-- The clockwise silhouette of `rr` (already assumed normalized) as
`(point, outward offset direction)` samples. Each rounded corner contributes
an arc of `cornerSegments`-many samples with exact (unit) radial normals; a
zero-radius corner contributes its single corner point with the **mitered**
diagonal offset `⟨±1, ±1⟩` — magnitude `√2 = 1/cos 45°`, so an offset of
`±d` along it lands exactly on both adjacent edges' lines offset by `d`
(`strokeSilhouette`'s `±n·w/2` then produces full-width edges and sharp
mitered corners, matching the GPU backend's SDF rect stroke). Consumers that
need positions only (`roundRectFill`) are unaffected — the sample *points*
are the exact corners either way. `.continuous` corners sample the
superellipse (`squirclePt`) with its own outward normals instead of the
circular arc. -/
def roundRectSilhouette (rr : RoundRect)
    (style : CornerStyle := .circular) : Array (Offset × Offset) := Id.run do
  let r := rr.rect
  let mut out : Array (Offset × Offset) := #[]
  -- (centerx, centery, rx, ry, startAngle, mitered offset for the zero case)
  let corners : Array (Float32 × Float32 × Float32 × Float32 × Float32 × Offset) := #[
    (r.left + rr.topLeft.x,     r.top + rr.topLeft.y,        rr.topLeft.x,     rr.topLeft.y,     piF,            ⟨-1, -1⟩),
    (r.right - rr.topRight.x,   r.top + rr.topRight.y,       rr.topRight.x,    rr.topRight.y,    piF * 1.5,      ⟨ 1, -1⟩),
    (r.right - rr.bottomRight.x, r.bottom - rr.bottomRight.y, rr.bottomRight.x, rr.bottomRight.y, 0,             ⟨ 1,  1⟩),
    (r.left + rr.bottomLeft.x,  r.bottom - rr.bottomLeft.y,  rr.bottomLeft.x,  rr.bottomLeft.y,  piF * 0.5,     ⟨-1,  1⟩)]
  for (cx, cy, rx, ry, a0, diag) in corners do
    if rx <= 1e-4 && ry <= 1e-4 then
      out := out.push (⟨cx, cy⟩, diag)
    else
      let segs := cornerSegments (max rx ry)
      for k in [0:segs + 1] do
        let a := a0 + piF / 2 * (k.toFloat32 / segs.toFloat32)
        match style with
        | .circular =>
          let p := ellipsePt ⟨cx, cy⟩ rx ry a
          -- radial outward normal on the ellipse boundary
          let nrm := norm ⟨(Float.cos a.toFloat).toFloat32, (Float.sin a.toFloat).toFloat32⟩
          out := out.push (p, nrm)
        | .continuous =>
          let p := squirclePt ⟨cx, cy⟩ rx ry a
          out := out.push (p, squircleNormal (p - ⟨cx, cy⟩) rx ry)
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
def roundRectFill (rr : RoundRect) (color : Color)
    (style : CornerStyle := .circular) : Mesh :=
  if rr.rect.isEmpty then .empty
  else fillPolygon ((roundRectSilhouette rr.normalize style).map (·.1)) color

/-- Stroked rounded rectangle, `width` centered on the boundary, feathered both
sides. Mirrors `DrawScope.drawRoundRect` with `Stroke` style. -/
def roundRectStroke (rr : RoundRect) (width : Float32) (color : Color)
    (style : CornerStyle := .circular) : Mesh :=
  if rr.rect.isEmpty then .empty
  else strokeSilhouette (roundRectSilhouette rr.normalize style) width color (closed := true)

-- The squircle silhouette: same sample count, meets the circular arc at the
-- quadrant endpoints (the edge joins, with ≈ the edge's axis normal — the
-- √|sin| parametrization turns the endpoint angle's float error ε into a
-- √ε ≈ 3e-4 px wobble, invisible but not exactly zero), every corner sample
-- sits 4-norm-exactly on r, and mid-corner it bulges beyond the circle.
#guard
  let sil := roundRectSilhouette (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .continuous
  let silC := roundRectSilhouette (RoundRect.circular ⟨0, 0, 40, 40⟩ 8)
  sil.size == silC.size
    && (sil[0]!.1 - silC[0]!.1).x.abs < 1e-2 && (sil[0]!.1 - silC[0]!.1).y.abs < 1e-2
    && (sil[0]!.2.x + 1).abs < 1e-3 && sil[0]!.2.y.abs < 1e-2
#guard
  let sil := roundRectSilhouette (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .continuous
  -- the first 8 samples are the top-left corner (`cornerSegments 8 = 7`)
  let pts := (sil.extract 0 8).map (·.1 - (⟨8, 8⟩ : Offset))
  pts.all (fun d =>
      let n4 := (d.x*d.x*d.x*d.x + d.y*d.y*d.y*d.y).sqrt.sqrt
      (n4 - 8).abs < 1e-3)
    && pts.any (fun d => (d.x*d.x + d.y*d.y).sqrt > 9.4)

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

/-! ## Elevation shadow (feathered ring approximation) -/

/-- Subdivide a closed silhouette so no segment is longer than `maxLen`
(inserted points lerp positions and re-normalize lerped normals) — shadow
rings sample a nonlinear falloff, so long straight edges need intermediate
samples for the interpolation to track it. -/
private def densify (samples : Array (Offset × Offset)) (maxLen : Float32) :
    Array (Offset × Offset) := Id.run do
  let n := samples.size
  let mut out : Array (Offset × Offset) := Array.emptyWithCapacity (2 * n)
  for i in [0:n] do
    let (p, np) := samples[i]!
    let (q, nq) := samples[(i + 1) % n]!
    out := out.push (p, np)
    let d := q - p
    let len := (d.x * d.x + d.y * d.y).sqrt
    let extra := (len / maxLen).toUInt64.toNat
    for k in [1:extra + 1] do
      let t := k.toFloat32 / (extra + 1).toFloat32
      out := out.push (Offset.lerp p q t, norm (Offset.lerp np nq t))
  return out

/-- A Gaussian drop shadow of a rounded rect, tessellated: the offset shape's
silhouette grows three outward rings at `σ`, `2σ`, `3σ` and three inward
rings (down to `3σ` inside, capped so they stay within the shape), all vertex
alphas sampling the *same* analytic shadow function the GPU shadow shader
evaluates (`Gpu.shadow`, Evan Wallace's form — `#guard`-tested in
`Gpu/Sdf.lean`), so the rasterizer's linear interpolation approximates the
GPU result on both sides of the edge — without the inner rings a large
shadow's interior would ramp linearly from the centroid instead of saturating
within `3σ` of the edge. The documented SDL-renderer shadow fallback;
`σ = blur / 2`. Zero blur degrades to a hard offset fill; empty rect or
transparent color → `Mesh.empty`. -/
def roundRectShadow (rr : RoundRect) (offset : Offset) (blur : Float32)
    (color : Color) : Mesh := Id.run do
  if rr.rect.isEmpty || color.a <= 0 then return .empty
  if blur <= 0 then return roundRectFill (rr.translate offset) color
  let rr := (rr.translate offset).normalize
  let sigma := max 0.5 (blur / 2)
  let o : Offset := ⟨rr.rect.left, rr.rect.top⟩
  let size : Size := ⟨rr.rect.width, rr.rect.height⟩
  let corner := rr.topLeft.x    -- per-corner radii degrade to the top-left one
  let alphaAt (p : Offset) : Float32 := color.a * Gpu.shadow p o size corner sigma
  let sil := densify (roundRectSilhouette rr) (max sigma 2)
  let n := sil.size
  if n < 3 then return .empty
  let centroid : Offset := ⟨o.x + size.width / 2, o.y + size.height / 2⟩
  -- ring offsets along the outward normal, innermost first; the inward depth
  -- is capped below the inradius so inner rings cannot cross the far side.
  let inDepth := min (3 * sigma) (min size.width size.height / 2 * 0.9)
  let offs : Array Float32 :=
    #[-inDepth, -inDepth * 2 / 3, -inDepth / 3, 0, sigma, 2 * sigma, 3 * sigma]
  let rings := offs.size
  let mut vs : Array DVertex := Array.emptyWithCapacity (rings * n + 1)
  vs := vs.push ⟨centroid, color.withAlpha (alphaAt centroid)⟩
  let mut ringIdx := 0
  for off in offs do
    for (p, nrm) in sil do
      let q := p + nrm * off
      -- the outermost ring is forced fully transparent for a clean edge
      vs := vs.push ⟨q, color.withAlpha (if ringIdx == rings - 1 then 0 else alphaAt q)⟩
    ringIdx := ringIdx + 1
  -- indices: interior fan to the innermost ring + a band per ring pair.
  let mut is : Array Int32 := Array.emptyWithCapacity (3 * n + 6 * (rings - 1) * n)
  for i in [0:n] do
    let j := (i + 1) % n
    is := pushTri is 0 (1 + i) (1 + j)
    for k in [0:rings - 1] do
      let a := 1 + k * n + i
      let b := 1 + k * n + j
      let c := 1 + (k + 1) * n + j
      let d := 1 + (k + 1) * n + i
      is := pushTri (pushTri is a b c) a c d
  return { vertices := vs, indices := is }

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
  if brush.isSolid then m
  else
    { m with vertices := m.vertices.map fun v =>
        let c := brush.colorAt v.pos
        { v with color := if v.color.a == 0 then c.withAlpha 0 else c } }

/-- Build a shape mesh from a tessellator that takes a single fill color: for a
solid brush the color is used directly; for a gradient the shape is tessellated
opaque then repainted per vertex (the tessellator emits a vertex per silhouette
point, so the rasterizer interpolates the gradient across the triangles). -/
def shapeMesh (brush : Brush) (mk : Color → Mesh) : Mesh :=
  if brush.isSolid then mk brush.primaryColor
  else paintMesh (mk Color.white) brush

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
  /-- A filled rounded rect (`roundRectFill`); `style` picks circular or
  squircle corners. -/
  | rrFill (rr : RoundRect) (brush : Brush) (style : CornerStyle := .circular)
  /-- A stroked rounded rect of pixel `width`, centered on the boundary
  (`roundRectStroke`); `style` picks circular or squircle corners. -/
  | rrStroke (rr : RoundRect) (width : Float32) (brush : Brush)
      (style : CornerStyle := .circular)
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
  /-- A Gaussian drop shadow under a rounded rect, displaced by `offset` with
  a blur of `blur` px (`σ = blur / 2`). The SDL backend tessellates it
  (`roundRectShadow`); the GPU backend evaluates the analytic form in its
  shadow shader. Recorded by `Modifier.shadow`. -/
  | rrShadow (rr : RoundRect) (offset : Offset) (blur : Float32) (color : Color)
  /-- An arbitrary vector path filled under its fill rule (`pathFillMesh` —
  the band-sweep tessellation is the path rasterization on *both* backends). -/
  | pathFill (path : Path) (brush : Brush)
  /-- A path fill restricted to a second path's interior — recorded by
  `drawPath` fills inside `DrawScope.clipPath`; `clip` is in the same local
  coordinates as `path` (`pathFillMeshClipped`, exact on both backends). -/
  | pathFillClipped (path clip : Path) (brush : Brush)
  /-- A path stroked with the full `Stroke` description — caps, joins, miter
  limit, dashing (`pathStrokeMesh`). -/
  | pathStroke (path : Path) (stroke : Stroke) (brush : Brush)
  deriving Repr, BEq, Inhabited

/-- Tessellate the mesh a `ShapeSpec` describes (a pure function — the spec
*is* the tessellation's full input). -/
def ShapeSpec.tessellate : ShapeSpec → Mesh
  | .rrFill rr brush style => shapeMesh brush (roundRectFill rr · style)
  | .rrStroke rr width brush style => shapeMesh brush (roundRectStroke rr width · style)
  | .circleFill center radius brush => shapeMesh brush (Compose.Draw.circleFill center radius)
  | .circleFillClipped center radius rr brush =>
    shapeMesh brush (circleFillClippedToRoundRect center radius rr)
  | .circleStroke center radius width brush =>
    shapeMesh brush (Compose.Draw.circleStroke center radius width)
  | .arcStroke center radius startRad sweepRad width brush =>
    shapeMesh brush (Compose.Draw.arcStroke center radius startRad sweepRad width)
  | .line p0 p1 width brush => shapeMesh brush (Compose.Draw.line p0 p1 width)
  | .rrShadow rr offset blur color => roundRectShadow rr offset blur color
  | .pathFill path brush => shapeMesh brush (fun c => pathFillMesh path c)
  | .pathFillClipped path clip brush => shapeMesh brush (fun c => pathFillMeshClipped path clip c)
  | .pathStroke path stroke brush => shapeMesh brush (fun c => pathStrokeMesh path stroke c)

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

/-- Conservative local-coordinate bounds of everything the spec can touch on
either backend: the geometry plus centered stroke halves, plus a 1-px AA
margin (the feather ring outside on SDL, the quad's inflated SDF edge on the
GPU). A shadow reaches `3σ + 1` beyond its displaced rect (the tessellator's
outermost ring / the shadow shader's vertex inflation). -/
def ShapeSpec.bounds : ShapeSpec → Rect
  | .rrFill rr _ _ => rr.rect.inflate 1
  | .rrStroke rr w _ _ => rr.rect.inflate (w / 2 + 1)
  | .circleFill c r _ => (Rect.mk (c.x - r) (c.y - r) (c.x + r) (c.y + r)).inflate 1
  | .circleFillClipped c r rr _ =>
    ((Rect.mk (c.x - r) (c.y - r) (c.x + r) (c.y + r)).intersect rr.rect).inflate 1
  | .circleStroke c r w _ =>
    (Rect.mk (c.x - r) (c.y - r) (c.x + r) (c.y + r)).inflate (w / 2 + 1)
  | .arcStroke c r _ _ w _ =>
    (Rect.mk (c.x - r) (c.y - r) (c.x + r) (c.y + r)).inflate (w / 2 + 1)
  | .line p0 p1 w _ =>
    (Rect.mk (min p0.x p1.x) (min p0.y p1.y) (max p0.x p1.x) (max p0.y p1.y)).inflate (w / 2 + 1)
  | .rrShadow rr off blur _ =>
    (rr.rect.translate off).inflate (3 * max 0.5 (blur / 2) + 1)
  | .pathFill path _ => path.bounds.inflate 1
  | .pathFillClipped path clip _ => (path.bounds.intersect clip.bounds).inflate 1
  | .pathStroke path stroke _ => path.bounds.inflate stroke.boundsPad

#guard (ShapeSpec.rrFill (RoundRect.ofRect ⟨10, 10, 30, 30⟩) (.solid .red)).bounds
        == (⟨9, 9, 31, 31⟩ : Rect)
#guard (ShapeSpec.circleStroke ⟨20, 20⟩ 10 4 (.solid .red)).bounds == (⟨7, 7, 33, 33⟩ : Rect)
#guard (ShapeSpec.line ⟨0, 10⟩ ⟨10, 0⟩ 2 (.solid .red)).bounds == (⟨-2, -2, 12, 12⟩ : Rect)
#guard (ShapeSpec.rrShadow (RoundRect.ofRect ⟨10, 10, 30, 30⟩) ⟨0, 2⟩ 8 .black).bounds
        == (⟨-3, -1, 43, 45⟩ : Rect)  -- σ = 4 → 3σ + 1 = 13 beyond the offset rect
-- The tessellated mesh never escapes the spec's bounds.
#guard
  let specs : List ShapeSpec := [
    .rrFill (RoundRect.circular ⟨10, 10, 50, 40⟩ 8) (.solid .red),
    .rrStroke (RoundRect.circular ⟨10, 10, 50, 40⟩ 8) 3 (.solid .red),
    .circleFill ⟨30, 30⟩ 15 (.solid .red),
    .circleFillClipped ⟨30, 30⟩ 25 (RoundRect.circular ⟨15, 15, 45, 45⟩ 6) (.solid .red),
    .circleStroke ⟨30, 30⟩ 15 4 (.solid .red),
    .arcStroke ⟨30, 30⟩ 15 0.5 2.5 4 (.solid .red),
    .line ⟨5, 40⟩ ⟨50, 8⟩ 3 (.solid .red),
    .rrShadow (RoundRect.circular ⟨10, 10, 50, 40⟩ 8) ⟨0, 2⟩ 6 .black,
    .pathFill (Path.build do
      PathM.moveTo ⟨10, 10⟩; PathM.quadTo ⟨45, 5⟩ ⟨45, 40⟩; PathM.lineTo ⟨10, 40⟩
      PathM.close) (.solid .red),
    .pathFillClipped (Path.build do PathM.addRect ⟨5, 5, 45, 45⟩)
      (Path.build do PathM.addOval ⟨10, 0, 50, 40⟩) (.solid .red),
    .pathStroke (Path.build do
        PathM.moveTo ⟨5, 40⟩; PathM.lineTo ⟨25, 5⟩; PathM.lineTo ⟨45, 40⟩)
      { width := 6, cap := .square, join := .miter, dash := some (#[9, 4], 0) }
      (.solid .red)]
  specs.all fun spec =>
    match spec.tessellate.bounds with
    | none => true
    | some b => (b.intersect spec.bounds) == b

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

-- Sharp-corner stroke thickness: a zero-radius rect stroke of width 4 keeps
-- the full perpendicular thickness (opaque band spans ±w/2 = [8, 12] across
-- the y = 10 top edge) and reaches the mitered outer corner — matching the
-- GPU backend's SDF rect stroke. (All older stroke guards use radius 8, which
-- is why the diagonal-normal thinning survived.)
#guard
  let m := roundRectStroke (RoundRect.ofRect ⟨10, 10, 50, 50⟩) 4 .red
  meshContains m ⟨30, 8.2⟩ (opaqueOnly := true)          -- outer half present
    && meshContains m ⟨30, 11.8⟩ (opaqueOnly := true)    -- inner half present
    && !meshContains m ⟨30, 7.4⟩ (opaqueOnly := true)    -- past ±w/2: feather…
    && meshContains m ⟨30, 7.4⟩                          -- …but still feathered
    && meshContains m ⟨8.3, 8.3⟩ (opaqueOnly := true)    -- mitered outer corner
    && meshContains m ⟨11.7, 11.7⟩ (opaqueOnly := true)  -- mitered inner corner
-- The fill silhouette is untouched by the mitered corner offsets (positions
-- are the exact corners; only the offset direction's magnitude changed).
#guard
  let s := roundRectSilhouette (RoundRect.ofRect ⟨10, 10, 50, 50⟩)
  s.map (·.1) == #[(⟨10, 10⟩ : Offset), ⟨50, 10⟩, ⟨50, 50⟩, ⟨10, 50⟩]

-- Open strokes feather their butt ends too: just past the end lies the
-- transparent end apron (and its corner wedges), past the apron nothing.
#guard
  let m := line ⟨0, 0⟩ ⟨10, 0⟩ 4 .red
  meshContains m ⟨10.5, 0⟩ && !meshContains m ⟨10.5, 0⟩ (opaqueOnly := true)
    && meshContains m ⟨-0.5, 0⟩ && !meshContains m ⟨-0.5, 0⟩ (opaqueOnly := true)
    && meshContains m ⟨10.3, 2.3⟩ && meshContains m ⟨10.3, -2.3⟩  -- corner wedges
    && !meshContains m ⟨11.5, 0⟩ && (line ⟨0, 0⟩ ⟨10, 0⟩ 4 .red).indicesInRange
#guard
  let m := arcStroke ⟨50, 50⟩ 20 0 (piF / 2) 4 .red   -- ends at (70,50) and (50,70)
  -- 0.5 px past the (50,70) end along the outward tangent (−x): apron only
  m.indicesInRange && meshContains m ⟨49.5, 70⟩ && !meshContains m ⟨49.5, 70⟩ (opaqueOnly := true)

-- Degenerate inputs never panic; they produce the empty mesh.
#guard (roundRectFill (RoundRect.ofRect ⟨0, 0, 0, 0⟩) .red).isEmpty
#guard (circleFill ⟨0, 0⟩ 0 .red).isEmpty
#guard (circleFill ⟨0, 0⟩ (-5) .red).isEmpty
#guard (circleStroke ⟨0, 0⟩ 10 0 .red).isEmpty
#guard (arcStroke ⟨0, 0⟩ 10 0 0 4 .red).isEmpty
#guard (line ⟨5, 5⟩ ⟨5, 5⟩ 2 .red).isEmpty
#guard (line ⟨0, 0⟩ ⟨10, 0⟩ 0 .red).isEmpty

-- Shadow mesh: well-formed; centroid of a large rect at small σ is nearly the
-- full shadow color; the innermost ring (3σ inside the edge) is already
-- saturated, so the interior fan is flat; the outermost ring is fully
-- transparent; degenerate inputs produce the empty mesh.
#guard (roundRectShadow (RoundRect.circular ⟨0, 0, 100, 100⟩ 8) ⟨0, 2⟩ 4 (Color.black.withAlpha 0.25)).indicesInRange
#guard
  let m := roundRectShadow (RoundRect.ofRect ⟨0, 0, 100, 100⟩) ⟨0, 0⟩ 4 Color.black
  (m.vertices[0]!.color.a - 1).abs < 0.01
#guard
  let m := roundRectShadow (RoundRect.ofRect ⟨0, 0, 100, 100⟩) ⟨0, 0⟩ 4 Color.black
  -- vertex 1 is a corner sample pushed inward along the mitered diagonal
  -- (3σ per axis)
  (m.vertices[1]!.color.a - 1).abs < 0.05
#guard
  let m := roundRectShadow (RoundRect.ofRect ⟨0, 0, 100, 100⟩) ⟨0, 0⟩ 4 Color.black
  let n := (m.vertices.size - 1) / 7
  m.vertices[1 + 6 * n]!.color.a == 0
-- Small shapes cap the inner rings inside the shape (no crossing).
#guard
  let m := roundRectShadow (RoundRect.ofRect ⟨0, 0, 8, 8⟩) ⟨0, 0⟩ 12 .black
  m.indicesInRange && m.vertices.all fun v =>
    (⟨-19, -19, 27, 27⟩ : Rect).contains v.pos
#guard (roundRectShadow (RoundRect.ofRect ⟨0, 0, 0, 0⟩) ⟨0, 2⟩ 4 .black).isEmpty
#guard (roundRectShadow (RoundRect.ofRect ⟨0, 0, 10, 10⟩) ⟨0, 2⟩ 4 (Color.black.withAlpha 0)).isEmpty
-- Zero blur degrades to the hard offset fill.
#guard roundRectShadow (RoundRect.ofRect ⟨0, 0, 10, 10⟩) ⟨0, 2⟩ 0 .black
        == roundRectFill (RoundRect.ofRect ⟨0, 2, 10, 12⟩) .black
#guard (ShapeSpec.rrShadow (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) ⟨0, 2⟩ 4 .black).tessellate
        == roundRectShadow (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) ⟨0, 2⟩ 4 .black

-- Clipping a fully-contained polygon returns it unchanged (all inside).
#guard (clipPolygon #[⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩] #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩]).size == 3
-- Clipping a circle far larger than the rrect yields a bounded (non-empty) fill.
#guard !(circleFillClippedToRoundRect ⟨20, 20⟩ 100 (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).isEmpty
-- Clipping a circle entirely outside the rrect yields an empty polygon.
#guard (circleFillClippedToRoundRect ⟨500, 500⟩ 5 (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) .red).isEmpty

end Compose.Draw

end
