module

public import Compose.Ui.Draw.Path
public meta import Compose.Ui.Draw.Path
public import Compose.Ui.Draw.Mesh
public meta import Compose.Ui.Draw.Mesh

public section

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

The same sweep also clips: `fillContours` optionally carries a second contour
set (the clip path) whose edges accumulate into a *separate* winding counter —
a span is inside iff the path's rule accepts its winding **and** the clip's
rule accepts the clip winding. That makes `clipPath`-ed path fills exact on
both backends (`ShapeSpec.pathFillClipped`), the `circleFillClipped`
precedent. With a clip, feather segments are first split at crossings with the
other set's edges so each piece classifies sidedness at its own midpoint.

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
winding contribution (`+1` downward, `-1` upward). `clipSrc` marks edges that
came from the clip path (they accumulate into the clip's winding counter). -/
private structure SweepEdge where
  a : Offset
  b : Offset
  w : Int
  clipSrc : Bool := false
  deriving Inhabited

/-- The edge's x at height `y` (callers keep `y` within `[a.y, b.y]`). -/
private def SweepEdge.xAt (e : SweepEdge) (y : Float32) : Float32 :=
  e.a.x + (y - e.a.y) / (e.b.y - e.a.y) * (e.b.x - e.a.x)

/-- Non-horizontal edges of closed contours, y-sorted per edge. Horizontal
segments carry no winding (the feather pass still anti-aliases them). -/
private def contourEdges (contours : Array (Array Offset)) (clipSrc : Bool := false) :
    Array SweepEdge := Id.run do
  let mut out : Array SweepEdge := #[]
  for pts in contours do
    let n := pts.size
    for i in [0:n] do
      let p := pts[i]!
      let q := pts[(i + 1) % n]!
      if p.y < q.y then out := out.push { a := p, b := q, w := 1, clipSrc }
      else if q.y < p.y then out := out.push { a := q, b := p, w := -1, clipSrc }
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

/-- Fill already-flat closed `contours` under `rule` via the band sweep
described in the module doc, feathered 1 px on the outside; an optional
`clip` contour set (with its own fill rule) restricts the fill exactly via a
second winding accumulator. The workhorse behind `pathFillMesh`,
`pathFillMeshClipped`, and the stroker's outline fill (`pathStrokeMesh`).
Degenerate input (no area, or a clip with no area) returns `Mesh.empty`. -/
def fillContours (contours : Array (Array Offset)) (rule : FillRule)
    (clip : Option (Array (Array Offset) × FillRule)) (color : Color) : Mesh := Id.run do
  let pEdges := contourEdges contours
  if pEdges.isEmpty then return .empty
  let cEdges := match clip with
    | some (cc, _) => contourEdges cc (clipSrc := true)
    | none => #[]
  if clip.isSome && cEdges.isEmpty then return .empty
  let edges := pEdges ++ cEdges
  let events := eventYs edges
  let hasClip := clip.isSome
  let clipRule := (clip.map (·.2)).getD .nonZero
  let insideW (wp wc : Int) : Bool :=
    rule.isInside wp && (!hasClip || clipRule.isInside wc)
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
    let mut wp : Int := 0
    let mut wc : Int := 0
    for ai in [0:actives.size] do
      let e := actives[ai]!
      if e.clipSrc then wc := wc + e.w else wp := wp + e.w
      if insideW wp wc && ai + 1 < actives.size then
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
  -- feather: a 1-px transparent apron on each boundary piece's unfilled side.
  -- Both contour sets feather (the clip's edges anti-alias where they crop the
  -- fill); with a clip, segments are first split at proper crossings with the
  -- *other* set's edges so a segment only partly on the boundary feathers
  -- exactly the boundary part (and never paints outside the clipped region).
  let insidePt (p : Offset) : Bool :=
    rule.isInside (polyWinding contours p) &&
      (match clip with | some (cc, rc) => rc.isInside (polyWinding cc p) | none => true)
  let fc := color.withAlpha 0
  let featherSets : Array (Array (Array Offset) × Array (Array Offset)) :=
    match clip with
    | some (cc, _) => #[(contours, cc), (cc, contours)]
    | none => #[(contours, #[])]
  for (set, others) in featherSets do
    for pts in set do
      let n := pts.size
      for i in [0:n] do
        let a := pts[i]!
        let b := pts[(i + 1) % n]!
        let d1 := b - a
        let nrm := perp (norm d1)
        if nrm != (⟨0, 0⟩ : Offset) then
          let mut ts : Array Float32 := #[]
          for opts in others do
            let on := opts.size
            for oi in [0:on] do
              let d2 := opts[(oi + 1) % on]! - opts[oi]!
              let denom := d1.x * d2.y - d1.y * d2.x
              if denom.abs > 1e-9 then
                let r := opts[oi]! - a
                let t := (r.x * d2.y - r.y * d2.x) / denom
                let u := (r.x * d1.y - r.y * d1.x) / denom
                -- u is closed: a cut where the other path's *vertex* touches
                -- this segment (a T-junction) is still a boundary transition
                if 0 < t && t < 1 && 0 <= u && u <= 1 then
                  ts := ts.push t
          let mut t0 : Float32 := 0
          for t1 in (ts.qsort (· < ·)).push 1 do
            if t1 - t0 > 1e-6 then
              let pa := Offset.lerp a b t0
              let pb := Offset.lerp a b t1
              let mid := Offset.lerp pa pb 0.5
              let plusIn := insidePt (mid + nrm * (0.05 : Float32))
              let minusIn := insidePt (mid - nrm * (0.05 : Float32))
              if plusIn != minusIn then
                let out := if plusIn then -nrm else nrm
                (vs, is) := quad pa pb (pb + out) (pa + out) color color fc fc vs is
              t0 := t1
  return { vertices := vs, indices := is }

/-- Fill an arbitrary path with `color`, feathered 1 px on the outside.
Gradient brushes ride on top via `shapeMesh` (the tessellator emits a vertex
per trapezoid corner, so per-vertex colors interpolate across the interior
like every other shape). -/
def pathFillMesh (path : Path) (color : Color) (tol : Float32 := 0.25) : Mesh :=
  fillContours ((path.flatten tol).map (·.1)) path.fillRule none color

/-- Fill `path` restricted to the interior of `clip` (each under its own fill
rule) — one band sweep over both edge sets, exact on both backends. Backs
`ShapeSpec.pathFillClipped` (recorded by `drawPath` fills inside
`DrawScope.clipPath`). -/
def pathFillMeshClipped (path clip : Path) (color : Color) (tol : Float32 := 0.25) : Mesh :=
  fillContours ((path.flatten tol).map (·.1)) path.fillRule
    (some ((clip.flatten tol).map (·.1), clip.fillRule)) color

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

/-- Whether `p` sits within `margin` of any segment of any contour (test
helper — samples this close to an edge are in the intentional AA band). -/
def nearContours (contours : Array (Array Offset)) (p : Offset)
    (margin : Float32 := 1.5) : Bool := Id.run do
  for pts in contours do
    let n := pts.size
    for i in [0:n] do
      if Offset.distToSegment p pts[i]! pts[(i + 1) % n]! < margin then
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
      if !nearContours contours p then
        if path.contains p tol then
          if !meshContains m p (opaqueOnly := true) then return false
        else
          if meshContains m p then return false
  return true

/-- `pathFillAgreesWithOracle` for the clipped sweep: samples ≥ 1.5 px from
*both* paths' edges must classify as `path.contains ∧ clip.contains`. The grid
covers the path's inflated bounds (the mesh cannot exist elsewhere), so
feather leaking outside the clip would fail the outside check. -/
def pathFillClippedAgreesWithOracle (path clip : Path) (tol : Float32 := 0.25) : Bool := Id.run do
  let m := pathFillMeshClipped path clip .red tol
  let contours := ((path.flatten tol) ++ (clip.flatten tol)).map (·.1)
  let b := (path.bounds).inflate 2
  let x0 := b.left.floor
  let y0 := b.top.floor
  let w := ((b.right - x0).toFloat.ceil.toUInt64.toNat) + 1
  let h := ((b.bottom - y0).toFloat.ceil.toUInt64.toNat) + 1
  for iy in [0:h] do
    for ix in [0:w] do
      let p : Offset := ⟨x0 + ix.toFloat32 + 0.5, y0 + iy.toFloat32 + 0.5⟩
      if !nearContours contours p then
        if path.contains p tol && clip.contains p tol then
          if !meshContains m p (opaqueOnly := true) then return false
        else
          if meshContains m p then return false
  return true

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

/-! ### Clipped fills -/

open PathM in
private def clipSquare : Path := Path.build do addRect ⟨0, 0, 10, 10⟩

-- A rect clipped by an overlapping rect fills exactly the intersection.
#guard
  let m := pathFillMeshClipped (Path.build do PathM.addRect ⟨4, 4, 20, 8⟩) clipSquare .red
  meshContains m ⟨6, 6⟩ (opaqueOnly := true) &&
    !meshContains m ⟨12, 6⟩ &&      -- inside path, outside clip
    !meshContains m ⟨2, 2⟩          -- inside clip, outside path
-- A clip entirely disjoint from the path clips everything out.
#guard (pathFillMeshClipped (Path.build do PathM.addRect ⟨20, 20, 30, 30⟩) clipSquare .red).isEmpty
-- A degenerate clip (no area) clips everything out.
#guard (pathFillMeshClipped rectPath (Path.build (PathM.moveTo ⟨5, 5⟩)) .red).isEmpty
-- The feather split: a path edge crossing the clip boundary must not paint
-- outside the clipped region — the whole mesh stays inside the intersected
-- bounds + 1 px.
#guard
  let m := pathFillMeshClipped (Path.build do PathM.addRect ⟨0, 0, 6, 12⟩) clipSquare .red
  match m.bounds with
  | none => false
  | some b => (b.intersect ((⟨0, 0, 6, 10⟩ : Rect).inflate 1)) == b
-- An even-odd ring as the *clip*: the fill shows in the ring, not the hole.
#guard
  let m := pathFillMeshClipped (Path.build do PathM.addRect ⟨0, 0, 30, 30⟩)
    (ringPath .evenOdd) .red
  meshContains m ⟨4, 15⟩ (opaqueOnly := true) && !meshContains m ⟨15, 15⟩

-- Clipped oracle agreement (path rule × clip shape combinations).
#guard pathFillClippedAgreesWithOracle rectPath clipSquare
#guard pathFillClippedAgreesWithOracle (starPath .nonZero)
        (Path.build do PathM.addRect ⟨0, 0, 26, 40⟩)
#guard pathFillClippedAgreesWithOracle (starPath .evenOdd)
        (Path.build do PathM.addRect ⟨10, 4, 40, 30⟩)
#guard pathFillClippedAgreesWithOracle blobPath (ringPath .evenOdd)
#guard pathFillClippedAgreesWithOracle (ringPath .nonZero)
        (Path.build do PathM.addOval ⟨2, 2, 28, 28⟩)

end Compose.Draw

end
