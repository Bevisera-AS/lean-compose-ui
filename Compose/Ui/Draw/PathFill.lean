import Compose.Ui.Draw.Path
import Compose.Ui.Draw.Mesh

/-!
# Path fill tessellation (`Compose/Ui/Draw/PathFill.lean`)

The band-sweep fill tessellator — how arbitrary vector paths become triangle
meshes on **both** backends (the SDL renderer rasterizes the mesh; the GPU
backend draws it through its mesh pipeline — no mask textures, no stencil, per
DESIGN.md). Pipeline: flatten the path → collect non-horizontal edges with
their winding sign → cut the y range at every edge endpoint *and* pairwise
edge intersection (so no two active edges cross inside a band) → per band,
sort actives by x at the band's midline, accumulate winding left to right, and
emit one trapezoid (two triangles) per inside span under the path's fill rule
→ finally, feather: every flattened boundary segment that separates inside
from outside grows a 1-px alpha-0 quad on its unfilled side (the same software
anti-aliasing convention as `Tessellate.lean`'s silhouette feather ring).

Holes, even-odd vs non-zero, and self-intersection all fall out of the winding
accumulation. Numeric edge cases (near-parallel edges, ε-close events)
degrade to a sliver band or a misplaced 1-px feather — never a crash or an
unbounded mesh: mid-band sampling never evaluates at an event y, and the
ε-dedup keeps bands non-degenerate. Event discovery is O(edges²) — fine at
icon scale (a Bentley–Ottmann sweep could replace it behind the same
signature if ever needed).

Everything is pure and `#guard`-tested against the geometric oracle
`Path.contains` over a sample grid (`pathFillAgreesWithOracle`).
-/

namespace Compose.Draw
open Compose

/-- Normalize to unit length; zero maps to itself. -/
private def norm (v : Offset) : Offset :=
  let len := (v.x * v.x + v.y * v.y).sqrt
  if len <= 1e-6 then ⟨0, 0⟩ else ⟨v.x / len, v.y / len⟩

/-- Right-hand perpendicular (`⟨x, y⟩ ↦ ⟨y, -x⟩`). -/
private def perp (d : Offset) : Offset := ⟨d.y, -d.x⟩

/-- One sweep edge: endpoints with `a.y < b.y` plus the original direction's
winding contribution (`+1` downward, `-1` upward). -/
private structure SweepEdge where
  a : Offset
  b : Offset
  w : Int
  deriving Inhabited

/-- The edge's x at height `y` (callers keep `y` within `[a.y, b.y]`). -/
private def SweepEdge.xAt (e : SweepEdge) (y : Float32) : Float32 :=
  e.a.x + (y - e.a.y) / (e.b.y - e.a.y) * (e.b.x - e.a.x)

/-- Non-horizontal edges of closed contours, y-sorted per edge. Horizontal
segments carry no winding (the feather pass still anti-aliases them). -/
private def contourEdges (contours : Array (Array Offset)) : Array SweepEdge := Id.run do
  let mut out : Array SweepEdge := #[]
  for pts in contours do
    let n := pts.size
    for i in [0:n] do
      let p := pts[i]!
      let q := pts[(i + 1) % n]!
      if p.y < q.y then out := out.push ⟨p, q, 1⟩
      else if q.y < p.y then out := out.push ⟨q, p, -1⟩
  return out

/-- Band-boundary ys: every edge endpoint plus every proper pairwise edge
intersection (T-junctions land on an endpoint event already), sorted and
ε-deduped so no band is degenerate and no two actives cross inside one. -/
private def eventYs (edges : Array SweepEdge) : Array Float32 := Id.run do
  let mut ys : Array Float32 := #[]
  for e in edges do
    ys := ys.push e.a.y |>.push e.b.y
  for i in [0:edges.size] do
    for j in [i+1:edges.size] do
      let e := edges[i]!
      let f := edges[j]!
      let d1 := e.b - e.a
      let d2 := f.b - f.a
      let denom := d1.x * d2.y - d1.y * d2.x
      if denom.abs > 1e-9 then
        let r := f.a - e.a
        let t := (r.x * d2.y - r.y * d2.x) / denom
        let u := (r.x * d1.y - r.y * d1.x) / denom
        if 0 < t && t < 1 && 0 < u && u < 1 then
          ys := ys.push (e.a.y + t * d1.y)
  let sorted := ys.qsort (· < ·)
  let mut out : Array Float32 := #[]
  for y in sorted do
    if out.isEmpty || y - out[out.size - 1]! > 1e-4 then
      out := out.push y
  return out

/-- Fill an arbitrary path with `color` via the band sweep described in the
module doc, feathered 1 px on the outside. Total: degenerate input (no area)
returns `Mesh.empty`. Gradient brushes ride on top via `shapeMesh` (the
tessellator emits a vertex per trapezoid corner, so per-vertex colors
interpolate across the interior like every other shape). -/
def pathFillMesh (path : Path) (color : Color) (tol : Float32 := 0.25) : Mesh := Id.run do
  let contours := (path.flatten tol).map (·.1)
  let edges := contourEdges contours
  if edges.isEmpty then return .empty
  let events := eventYs edges
  let inside := path.fillRule.isInside
  let mut vs : Array DVertex := #[]
  let mut is : Array Int32 := #[]
  let quad (a b c d : Offset) (ca cb cc cd : Color) (vs : Array DVertex)
      (is : Array Int32) : Array DVertex × Array Int32 :=
    let base := Int32.ofNat vs.size
    (vs.push ⟨a, ca⟩ |>.push ⟨b, cb⟩ |>.push ⟨c, cc⟩ |>.push ⟨d, cd⟩,
     is.push base |>.push (base + 1) |>.push (base + 2)
       |>.push base |>.push (base + 2) |>.push (base + 3))
  -- interior trapezoids
  for bi in [0:events.size - 1] do
    let y0 := events[bi]!
    let y1 := events[bi + 1]!
    let midY := (y0 + y1) / 2
    let actives := (edges.filter fun e => e.a.y <= midY && midY <= e.b.y)
      |>.qsort (fun e f => e.xAt midY < f.xAt midY)
    let mut w : Int := 0
    for ai in [0:actives.size] do
      let e := actives[ai]!
      w := w + e.w
      if inside w && ai + 1 < actives.size then
        let f := actives[ai + 1]!
        let xl0 := e.xAt y0
        let xr0 := f.xAt y0
        let xl1 := e.xAt y1
        let xr1 := f.xAt y1
        if xr0 - xl0 > 1e-6 || xr1 - xl1 > 1e-6 then
          let base := Int32.ofNat vs.size
          if xr0 - xl0 <= 1e-6 then
            -- top edge collapses (edges meet at the band top): one triangle
            vs := vs.push ⟨⟨xl0, y0⟩, color⟩ |>.push ⟨⟨xr1, y1⟩, color⟩
               |>.push ⟨⟨xl1, y1⟩, color⟩
            is := is.push base |>.push (base + 1) |>.push (base + 2)
          else if xr1 - xl1 <= 1e-6 then
            -- bottom edge collapses: one triangle
            vs := vs.push ⟨⟨xl0, y0⟩, color⟩ |>.push ⟨⟨xr0, y0⟩, color⟩
               |>.push ⟨⟨xl1, y1⟩, color⟩
            is := is.push base |>.push (base + 1) |>.push (base + 2)
          else
            (vs, is) := quad ⟨xl0, y0⟩ ⟨xr0, y0⟩ ⟨xr1, y1⟩ ⟨xl1, y1⟩
              color color color color vs is
  if is.isEmpty then return .empty
  -- feather: a 1-px transparent apron on each boundary segment's unfilled side
  let fc := color.withAlpha 0
  for pts in contours do
    let n := pts.size
    for i in [0:n] do
      let a := pts[i]!
      let b := pts[(i + 1) % n]!
      let nrm := perp (norm (b - a))
      if nrm != (⟨0, 0⟩ : Offset) then
        let mid := Offset.lerp a b 0.5
        let plusIn := inside (polyWinding contours (mid + nrm * (0.05 : Float32)))
        let minusIn := inside (polyWinding contours (mid - nrm * (0.05 : Float32)))
        if plusIn != minusIn then
          let out := if plusIn then -nrm else nrm
          (vs, is) := quad a b (b + out) (a + out) color color fc fc vs is
  return { vertices := vs, indices := is }

/-! ## Test oracle helpers

Public because the runtime fuzz group (`test/ComposeTests/PathDraw.lean`)
drives the same oracle over random polygons; not part of the drawing API. -/

/-- Whether `p` lies inside some triangle of `m`; `opaqueOnly` skips triangles
touching a feather vertex (alpha 0). Zero-area triangles never contain
anything (a rasterizer covers no pixel with them). Test helper — linear
scan. -/
def meshContains (m : Mesh) (p : Offset) (opaqueOnly : Bool := false) : Bool := Id.run do
  let cross (o q r : Offset) : Float32 :=
    (q.x - o.x) * (r.y - o.y) - (q.y - o.y) * (r.x - o.x)
  for t in [0:m.indices.size / 3] do
    let va := m.vertices[m.indices[3 * t]!.toNatClampNeg]!
    let vb := m.vertices[m.indices[3 * t + 1]!.toNatClampNeg]!
    let vc := m.vertices[m.indices[3 * t + 2]!.toNatClampNeg]!
    if !(opaqueOnly && (va.color.a == 0 || vb.color.a == 0 || vc.color.a == 0))
        && (cross va.pos vb.pos vc.pos).abs > 1e-6 then
      let d1 := cross va.pos vb.pos p
      let d2 := cross vb.pos vc.pos p
      let d3 := cross vc.pos va.pos p
      if (d1 >= 0 && d2 >= 0 && d3 >= 0) || (d1 <= 0 && d2 <= 0 && d3 <= 0) then
        return true
  return false

/-- The tessellator-vs-oracle agreement test: over an integer+½ grid across
the path's inflated bounds, every sample ≥ 1.5 px away from all flattened
edges classifies identically — inside samples land in an opaque triangle,
outside samples in no triangle at all (the feather apron only reaches 1 px
out). Samples near edges are skipped (that 1-px ring is the anti-aliasing
band, where coverage is intentionally fractional). -/
def pathFillAgreesWithOracle (path : Path) (tol : Float32 := 0.25) : Bool := Id.run do
  let m := pathFillMesh path .red tol
  let contours := (path.flatten tol).map (·.1)
  let b := (path.bounds).inflate 2
  let x0 := b.left.floor
  let y0 := b.top.floor
  let w := ((b.right - x0).toFloat.ceil.toUInt64.toNat) + 1
  let h := ((b.bottom - y0).toFloat.ceil.toUInt64.toNat) + 1
  for iy in [0:h] do
    for ix in [0:w] do
      let p : Offset := ⟨x0 + ix.toFloat32 + 0.5, y0 + iy.toFloat32 + 0.5⟩
      let mut near := false
      for pts in contours do
        let n := pts.size
        for i in [0:n] do
          if Offset.distToSegment p pts[i]! pts[(i + 1) % n]! < 1.5 then
            near := true
      if !near then
        if path.contains p tol then
          if !meshContains m p (opaqueOnly := true) then return false
        else
          if meshContains m p then return false
  return true

/-! ## Provisional stroke sampling (replaced by the real stroker in M-e2) -/

/-- `(point, unit normal)` samples of a flattened polyline: each point's
normal averages its adjacent segments' perpendiculars (endpoints of an open
line take their single segment's). Feeds `strokeSilhouette` for the
provisional `drawPath` stroke. -/
def polylineNormals (pts : Array Offset) (closed : Bool) : Array (Offset × Offset) := Id.run do
  let n := pts.size
  if n < 2 then return #[]
  let mut out : Array (Offset × Offset) := Array.emptyWithCapacity n
  for i in [0:n] do
    let d1 := if i > 0 then norm (pts[i]! - pts[i - 1]!)
      else if closed then norm (pts[i]! - pts[n - 1]!) else ⟨0, 0⟩
    let d2 := if i + 1 < n then norm (pts[i + 1]! - pts[i]!)
      else if closed then norm (pts[0]! - pts[i]!) else ⟨0, 0⟩
    let d := norm (d1 + d2)
    let dir := if d == (⟨0, 0⟩ : Offset) then (if d2 == (⟨0, 0⟩ : Offset) then d1 else d2) else d
    out := out.push (pts[i]!, perp dir)
  return out

#guard polylineNormals #[⟨0, 0⟩, ⟨10, 0⟩] false == #[(⟨0, 0⟩, ⟨0, -1⟩), (⟨10, 0⟩, ⟨0, -1⟩)]
#guard (polylineNormals #[⟨5, 5⟩] false).isEmpty

/-! ## `#guard` corpus

The oracle corpus from the plan: rect, ring with a hole (both rules), disjoint
squares, self-intersecting bowtie, five-point star under both rules, a cubic
blob, and degenerate paths. Each mesh is well-formed, stays inside the spec
bounds (`Path.bounds` + 1 px feather), and classifies every off-edge grid
sample exactly like `Path.contains`. -/

open PathM in
private def rectPath : Path := Path.build do addRect ⟨2, 2, 22, 14⟩

open PathM in
private def ringPath (rule : FillRule) : Path :=
  Path.build (fillRule := rule) do
    addRect ⟨0, 0, 30, 30⟩
    -- inner square reversed (counter-clockwise) so non-zero also sees the hole
    moveTo ⟨9, 9⟩; lineTo ⟨9, 21⟩; lineTo ⟨21, 21⟩; lineTo ⟨21, 9⟩; close

open PathM in
private def disjointPath : Path := Path.build do
  addRect ⟨0, 0, 10, 10⟩
  addRect ⟨20, 4, 32, 16⟩

open PathM in
private def bowtiePath : Path := Path.build do
  moveTo ⟨0, 0⟩; lineTo ⟨20, 20⟩; lineTo ⟨20, 0⟩; lineTo ⟨0, 20⟩; close

/-- Five-point star drawn by connecting every second pentagon vertex —
self-intersecting; the center winds twice (non-zero fills it, even-odd
leaves the pentagon hole). -/
private def starPath (rule : FillRule) : Path :=
  Path.build (fillRule := rule) (body := do
    let pt (k : Nat) : Offset :=
      let pi : Float := 3.14159265358979323846
      let a := -pi / 2 + k.toFloat * 4 * pi / 5
      ⟨20 + 18 * (Float.cos a).toFloat32, 20 + 18 * (Float.sin a).toFloat32⟩
    PathM.moveTo (pt 0)
    for k in [1:5] do
      PathM.lineTo (pt k)
    PathM.close)

open PathM in
private def blobPath : Path := Path.build do
  moveTo ⟨5, 15⟩
  cubicTo ⟨0, 0⟩ ⟨30, 0⟩ ⟨25, 15⟩
  cubicTo ⟨30, 30⟩ ⟨0, 30⟩ ⟨5, 15⟩
  close

-- Fill-rule discrimination at the star center, mesh-level.
#guard meshContains (pathFillMesh (starPath .nonZero) .red) ⟨20, 20⟩ (opaqueOnly := true)
#guard !meshContains (pathFillMesh (starPath .evenOdd) .red) ⟨20, 20⟩
#guard (starPath .nonZero).windingAt ⟨20, 20⟩ == 2

-- Well-formedness + bounds containment across the corpus.
#guard
  let specs := #[rectPath, ringPath .nonZero, ringPath .evenOdd, disjointPath, bowtiePath,
    starPath .nonZero, starPath .evenOdd, blobPath]
  specs.all fun p =>
    let m := pathFillMesh p .red
    m.indicesInRange &&
      (match m.bounds with
       | none => true
       | some b => (b.intersect (p.bounds.inflate 1)) == b)

-- The oracle agreement corpus (the tessellator's main correctness pin).
#guard pathFillAgreesWithOracle rectPath
#guard pathFillAgreesWithOracle (ringPath .nonZero)
#guard pathFillAgreesWithOracle (ringPath .evenOdd)
#guard pathFillAgreesWithOracle disjointPath
#guard pathFillAgreesWithOracle bowtiePath
#guard pathFillAgreesWithOracle (starPath .nonZero)
#guard pathFillAgreesWithOracle (starPath .evenOdd)
#guard pathFillAgreesWithOracle blobPath

-- Degenerate paths produce the empty mesh, never a panic.
#guard (pathFillMesh (Path.mk #[] .nonZero) .red).isEmpty
#guard (pathFillMesh (Path.build (PathM.moveTo ⟨5, 5⟩)) .red).isEmpty
open PathM in
#guard (pathFillMesh (Path.build do moveTo ⟨0, 0⟩; lineTo ⟨10, 10⟩; close) .red).isEmpty

end Compose.Draw
