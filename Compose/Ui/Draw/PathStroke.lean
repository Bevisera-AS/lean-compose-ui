import Compose.Ui.Draw.PathFill

/-!
# Path stroking (`Compose/Ui/Draw/PathStroke.lean`)

The stroker: caps, joins, miter limit, and dashing for `drawPath`. The
approach is Skia's stroke-to-fill: `strokeOutline` turns a flattened polyline
into a bag of consistently-wound convex contours — one rectangle per segment,
one wedge (miter/bevel/arc fan) per join, one cap piece per open end — and
`pathStrokeMesh` fills that bag through the M-e1 band sweep under the
**non-zero** rule. Overlap between the pieces (tight joins, self-crossing
spines, abutting dashes) simply winds ≥ 2 and stays filled once, so a bad join
is at worst a local shape error, never a broken mesh; seams interior to the
union get no feather (both sides classify inside), so the result anti-aliases
exactly like a single fill.

Dashing is a pure arc-length split (`dashSplit`) that runs *before* offsetting;
each dash strokes as an open polyline with the stroke's caps. A closed contour
dashes as the open walk around it — when the pattern is "on" across the start
point, the two abutting butt-capped dashes rejoin seamlessly through the
winding union.

Pure geometry, no SDL, no `IO`; heavily `#guard`-tested (exact arithmetic for
`dashSplit`, mesh-membership probes for caps/joins). Mirrors
`androidx.compose.ui.graphics.drawscope.Stroke` + `PathEffect.dashPathEffect`.
-/

namespace Compose.Draw
open Compose

/-- π as a `Float32` (Lean's stdlib has no `Float.pi`). -/
private def piF : Float32 := 3.14159265358979323846

/-- Normalize to unit length; zero maps to itself. -/
private def norm (v : Offset) : Offset :=
  let len := (v.x * v.x + v.y * v.y).sqrt
  if len <= 1e-6 then ⟨0, 0⟩ else ⟨v.x / len, v.y / len⟩

/-- Right-hand perpendicular (`⟨x, y⟩ ↦ ⟨y, -x⟩`). -/
private def perp (d : Offset) : Offset := ⟨d.y, -d.x⟩

/-- How an open stroke end is finished. Mirrors
`androidx.compose.ui.graphics.StrokeCap`. -/
inductive StrokeCap where
  /-- Flat end exactly at the endpoint. -/
  | butt
  /-- Semicircular bulge of radius `width / 2`. -/
  | round
  /-- Flat end extended `width / 2` past the endpoint. -/
  | square
  deriving Repr, BEq, Inhabited

/-- How two stroked segments connect at a vertex. Mirrors
`androidx.compose.ui.graphics.StrokeJoin`. -/
inductive StrokeJoin where
  /-- Sharp corner up to `miterLimit`, then bevel. -/
  | miter
  /-- Circular arc fan on the outer side. -/
  | round
  /-- Straight chord across the outer corner. -/
  | bevel
  deriving Repr, BEq, Inhabited

/-- A full stroke description for `drawPath`: pixel `width` centered on the
path, caps, joins with `miterLimit` (the maximum ratio of miter length to
`width / 2` before a miter falls back to bevel), and an optional
`(intervals, phase)` dash pattern — alternating on/off arc lengths starting
"on", shifted by `phase` (wraps). A pattern is ignored unless it has an even
count ≥ 2 of non-negative intervals with a positive total. Mirrors
`drawscope.Stroke` (+ `dashPathEffect`). -/
structure Stroke where
  width : Float32
  cap : StrokeCap := .butt
  join : StrokeJoin := .miter
  miterLimit : Float32 := 4
  dash : Option (Array Float32 × Float32) := none
  deriving Repr, BEq, Inhabited

/-- How far past `Path.bounds` a stroke can reach: half the width scaled by
the worst protrusion (miter tips up to `miterLimit ×`, square-cap corners
`√2 ×`), plus the 1-px feather — the `ShapeSpec.pathStroke` bounds pad. -/
def Stroke.boundsPad (s : Stroke) : Float32 :=
  let joinF : Float32 := match s.join with | .miter => max s.miterLimit 1 | _ => 1
  let capF : Float32 := match s.cap with | .square => 1.4142136 | _ => 1
  s.width / 2 * max joinF capF + 1

#guard ({ width := 4 } : Stroke).boundsPad == 9          -- miter limit 4 dominates
#guard ({ width := 4, join := .bevel } : Stroke).boundsPad == 3
#guard ({ width := 4, join := .round, cap := .square } : Stroke).boundsPad == 2 * 1.4142136 + 1

/-! ## Dashing -/

/-- Split a polyline into its "on" runs by arc length under `intervals`
(alternating on/off lengths, starting "on") shifted by `phase` (wraps, may be
negative). Returns open sub-polylines; cut points are lerped on their segment
and interior vertices are kept. A closed polyline is dashed as the open walk
around it, closing segment included (abutting first/last dashes rejoin through
the winding union). Assumes a validated pattern (even count ≥ 2, non-negative,
positive total — `strokeOutline` checks); a non-positive total yields `#[]`. -/
def dashSplit (pts : Array Offset) (closed : Bool) (intervals : Array Float32)
    (phase : Float32) : Array (Array Offset) := Id.run do
  if pts.size < 2 then return #[]
  let total := intervals.foldl (fun a v => a + max v 0) 0
  if total <= 1e-6 then return #[]
  let walk := if closed then pts.push pts[0]! else pts
  let m := walk.size
  -- cumulative arc length up to each walk point
  let mut cum : Array Float32 := #[0]
  for i in [1:m] do
    cum := cum.push (cum[i - 1]! + Offset.distance walk[i - 1]! walk[i]!)
  let totalLen := cum[m - 1]!
  if totalLen <= 1e-6 then return #[]
  -- pattern position at arc length 0, wrapped into [0, total)
  let startPos :=
    let f := phase - (phase / total).floor * total
    if f < 0 then f + total else f
  -- cumulative pattern-interval starts
  let mut cumInt : Array Float32 := #[0]
  for v in intervals do
    cumInt := cumInt.push (cumInt[cumInt.size - 1]! + max v 0)
  -- every "on" run, clamped to [0, totalLen]
  let periods := ((totalLen + startPos) / total).toFloat.ceil.toUInt64.toNat + 1
  let mut runs : Array (Float32 × Float32) := #[]
  for k in [0:periods] do
    for j in [0:intervals.size] do
      if j % 2 == 0 then
        let base := k.toFloat32 * total - startPos
        let a := max (cumInt[j]! + base) 0
        let b := min (cumInt[j + 1]! + base) totalLen
        if b - a > 1e-6 then
          runs := runs.push (a, b)
  -- extract each run's sub-polyline
  let mut out : Array (Array Offset) := #[]
  for (a, b) in runs do
    let mut dash : Array Offset := #[]
    for i in [0:m - 1] do
      let s0 := cum[i]!
      let s1 := cum[i + 1]!
      if s1 - s0 > 1e-9 && s1 > a && s0 < b then
        let at' (s : Float32) : Offset := Offset.lerp walk[i]! walk[i + 1]! ((s - s0) / (s1 - s0))
        if dash.isEmpty then
          dash := dash.push (if a <= s0 then walk[i]! else at' a)
        dash := dash.push (if b >= s1 then walk[i + 1]! else at' b)
    if dash.size >= 2 then
      out := out.push dash
  return out

section
private def approxOff (a b : Offset) (tol : Float32 := 0.001) : Bool :=
  (a.x - b.x).abs <= tol && (a.y - b.y).abs <= tol

private def approxDashes (got : Array (Array Offset)) (want : Array (Array Offset)) : Bool :=
  got.size == want.size &&
    (Array.range got.size).all fun i =>
      got[i]!.size == want[i]!.size &&
        (Array.range got[i]!.size).all fun j => approxOff got[i]![j]! want[i]![j]!

-- A 10-long line under (on 4, off 2): dashes [0,4] and [6,10].
#guard approxDashes (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩] false #[4, 2] 0)
        #[#[⟨0, 0⟩, ⟨4, 0⟩], #[⟨6, 0⟩, ⟨10, 0⟩]]
-- Phase 5 starts mid-"off" (1 left): dashes [1,5] and [7,10].
#guard approxDashes (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩] false #[4, 2] 5)
        #[#[⟨1, 0⟩, ⟨5, 0⟩], #[⟨7, 0⟩, ⟨10, 0⟩]]
-- Negative phase wraps: -2 ≡ 4 (mod 6) → dashes [2,6] and [8,10].
#guard approxDashes (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩] false #[4, 2] (-2))
        #[#[⟨2, 0⟩, ⟨6, 0⟩], #[⟨8, 0⟩, ⟨10, 0⟩]]
-- A closed square (perimeter 40) under (6,4): four dashes, one per side.
#guard (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] true #[6, 4] 0).size == 4
-- A dash spanning a corner keeps the interior vertex: run [0,12] crosses (10,0).
#guard approxDashes (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩] true #[12, 28] 0)
        #[#[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 2⟩]]
-- Degenerate patterns yield nothing.
#guard (dashSplit #[⟨0, 0⟩, ⟨10, 0⟩] false #[0, 0] 0).isEmpty
#guard (dashSplit #[⟨5, 5⟩] false #[4, 2] 0).isEmpty
end

/-! ## Outline construction -/

/-- Drop consecutive ε-duplicate points (and, for `closed`, a last point equal
to the first) so segment directions are always well-defined. -/
private def dedupe (pts : Array Offset) (closed : Bool) : Array Offset := Id.run do
  let mut out : Array Offset := #[]
  for p in pts do
    if out.isEmpty || Offset.distance p out[out.size - 1]! > 1e-6 then
      out := out.push p
  if closed && out.size > 1 && Offset.distance out[0]! out[out.size - 1]! <= 1e-6 then
    out := out.pop
  return out

/-- Points of the arc `c + rot(u0, t) · h` for `t` from `0` to `sweep`
(inclusive), ~2 px per segment. `u0` is a unit direction; positive `sweep`
turns clockwise on screen (y-down). -/
private def arcPts (c : Offset) (u0 : Offset) (sweep h : Float32) : Array Offset := Id.run do
  let segs := max 2 ((sweep.abs * h / 2).toFloat.ceil.toUInt64.toNat)
  let mut out : Array Offset := Array.emptyWithCapacity (segs + 1)
  for k in [0:segs + 1] do
    let t := (sweep * k.toFloat32 / segs.toFloat32).toFloat
    let cs := (Float.cos t).toFloat32
    let sn := (Float.sin t).toFloat32
    out := out.push ⟨c.x + (u0.x * cs - u0.y * sn) * h, c.y + (u0.x * sn + u0.y * cs) * h⟩
  return out

/-- The stroke pieces of one deduplicated polyline: segment rectangles, join
wedges, and (when open) end caps — every contour wound clockwise (+1). -/
private def strokePolyline (pts : Array Offset) (closed : Bool) (s : Stroke)
    (h : Float32) : Array (Array Offset) := Id.run do
  let n := pts.size
  if n < 2 then return #[]
  let mut out : Array (Array Offset) := #[]
  -- segment rectangles
  let segs := if closed then n else n - 1
  for i in [0:segs] do
    let p := pts[i]!
    let q := pts[(i + 1) % n]!
    let nr := perp (norm (q - p))
    out := out.push #[p + nr * h, q + nr * h, q - nr * h, p - nr * h]
  -- join wedges (every vertex when closed, interior vertices when open)
  let joins := if closed then n else n - 2
  for k in [0:joins] do
    let i := if closed then k else k + 1
    let v := pts[i]!
    let d1 := norm (v - pts[(i + n - 1) % n]!)
    let d2 := norm (pts[(i + 1) % n]! - v)
    let cross := d1.x * d2.y - d1.y * d2.x
    if cross.abs <= 1e-6 then
      -- collinear: nothing to join; a full reversal leaves a butt tip unless
      -- the join is round (semicircle, like a round cap)
      if Offset.dot d1 d2 < 0 && s.join == .round then
        out := out.push (arcPts v (perp d1) piF h)
    else
      let sign : Float32 := if cross > 0 then 1 else -1
      let u1 := perp d1 * sign
      let u2 := perp d2 * sign
      -- outer offset directions ordered for clockwise winding
      let (ua, ub) := if cross > 0 then (u1, u2) else (u2, u1)
      match s.join with
      | .bevel => out := out.push #[v, v + ua * h, v + ub * h]
      | .miter =>
        let m := norm (u1 + u2)
        let cosHalf := Offset.dot m u1
        if cosHalf > 1e-3 && 1 / cosHalf <= s.miterLimit then
          out := out.push #[v, v + ua * h, v + m * (h / cosHalf), v + ub * h]
        else
          out := out.push #[v, v + ua * h, v + ub * h]
      | .round =>
        let sweep := (Float.atan2 (ua.x * ub.y - ua.y * ub.x).toFloat
          (Offset.dot ua ub).toFloat).toFloat32
        out := out.push (#[v] ++ arcPts v ua sweep h)
  -- end caps
  if !closed then
    let cap (p e : Offset) : Array (Array Offset) :=   -- e = outward unit direction
      match s.cap with
      | .butt => #[]
      | .square =>
        let nr := perp e
        #[#[p + nr * h, p + nr * h + e * h, p - nr * h + e * h, p - nr * h]]
      | .round => #[arcPts p (perp e) piF h]
    out := out ++ cap pts[0]! (norm (pts[0]! - pts[1]!))
    out := out ++ cap pts[n - 1]! (norm (pts[n - 1]! - pts[n - 2]!))
  return out

/-- The stroke outline of one flattened polyline as consistently-wound convex
contours (segment rectangles + join wedges + caps, dashes pre-split) — fill
under the non-zero rule to rasterize (`pathStrokeMesh`). Width ≤ 0 or fewer
than two distinct points yields `#[]`. -/
def strokeOutline (pts : Array Offset) (closed : Bool) (s : Stroke) :
    Array (Array Offset) := Id.run do
  if s.width <= 0 then return #[]
  let pts := dedupe pts closed
  if pts.size < 2 then return #[]
  let h := s.width / 2
  let validDash := match s.dash with
    | some (ints, phase) =>
      if ints.size >= 2 && ints.size % 2 == 0 && ints.all (· >= 0)
          && ints.foldl (· + ·) 0 > 1e-6 then some (ints, phase) else none
    | none => none
  match validDash with
  | some (ints, phase) =>
    let mut out : Array (Array Offset) := #[]
    for dash in dashSplit pts closed ints phase do
      out := out ++ strokePolyline dash false s h
    return out
  | none => return strokePolyline pts closed s h

/-- Stroke an arbitrary path: flatten, outline every contour, and fill the
outline bag through the band sweep (non-zero — overlaps at joins and dash
seams resolve by winding). Gradient brushes ride on top via `shapeMesh`. -/
def pathStrokeMesh (path : Path) (s : Stroke) (color : Color)
    (tol : Float32 := 0.25) : Mesh :=
  let contours := (path.flatten tol).foldl (init := #[]) fun acc (pts, closed) =>
    acc ++ strokeOutline pts closed s
  fillContours contours .nonZero none color

/-! ## `#guard` tests

Caps and joins are pinned semantically: stroke a tiny polyline, fill the
outline, and probe mesh membership at points that discriminate the variants
(the same `meshContains` oracle style as `PathFill.lean`). -/

private def outlineMesh (pts : Array Offset) (closed : Bool) (s : Stroke) : Mesh :=
  fillContours (strokeOutline pts closed s) .nonZero none .red

-- A bare horizontal segment, width 4: spine opaque, beyond the butt end empty.
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨10, 0⟩] false { width := 4 }
  meshContains m ⟨5, 0⟩ (opaqueOnly := true) && meshContains m ⟨5, 1.5⟩ (opaqueOnly := true)
    && !meshContains m ⟨5, 3.5⟩ && !meshContains m ⟨-2, 0⟩
-- Square cap: extends w/2 past the end (corners included); round cap: extends
-- w/2 on the axis but stays inside the disc (the corner probe discriminates).
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨10, 0⟩] false { width := 4, cap := .square }
  meshContains m ⟨-1.5, 0⟩ (opaqueOnly := true)
    && meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true)
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨10, 0⟩] false { width := 4, cap := .round }
  meshContains m ⟨-1.5, 0⟩ (opaqueOnly := true)
    && !meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true)   -- 2.4 px out > radius 2
    && !meshContains m ⟨-2.5, 2.5⟩                          -- past the feather entirely
-- Right-angle L, width 4: the miter tip (≈ 2.83 px out on the diagonal) is
-- filled under miter, cut under bevel, rounded under round.
#guard
  let m := outlineMesh #[⟨0, 10⟩, ⟨0, 0⟩, ⟨10, 0⟩] false { width := 4, join := .miter }
  meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true) && meshContains m ⟨-0.8, -0.8⟩ (opaqueOnly := true)
#guard
  let m := outlineMesh #[⟨0, 10⟩, ⟨0, 0⟩, ⟨10, 0⟩] false { width := 4, join := .bevel }
  !meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true) && meshContains m ⟨-0.8, -0.8⟩ (opaqueOnly := true)
#guard
  let m := outlineMesh #[⟨0, 10⟩, ⟨0, 0⟩, ⟨10, 0⟩] false { width := 4, join := .round }
  !meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true)        -- 2.4 px out > radius 2
    && meshContains m ⟨-1.2, -1.2⟩ (opaqueOnly := true)    -- 1.7 px out < radius 2
-- A right angle's miter ratio is √2 ≈ 1.414: limit 1.2 falls back to bevel.
#guard
  let m := outlineMesh #[⟨0, 10⟩, ⟨0, 0⟩, ⟨10, 0⟩] false
    { width := 4, join := .miter, miterLimit := 1.2 }
  !meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true)
-- Full reversal: round join caps the turnaround with a semicircle; miter
-- leaves a butt tip (the overlapping rectangles still fill the spine once).
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨10, 0⟩, ⟨0, 0⟩] false { width := 4, join := .round }
  meshContains m ⟨11.5, 0⟩ (opaqueOnly := true) && meshContains m ⟨5, 0⟩ (opaqueOnly := true)
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨10, 0⟩, ⟨0, 0⟩] false { width := 4, join := .miter }
  !meshContains m ⟨11.5, 0⟩ && meshContains m ⟨5, 0⟩ (opaqueOnly := true)
-- A closed square outline rings the boundary and leaves the interior open.
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨20, 0⟩, ⟨20, 20⟩, ⟨0, 20⟩] true { width := 4 }
  meshContains m ⟨10, 0⟩ (opaqueOnly := true) && meshContains m ⟨0, 10⟩ (opaqueOnly := true)
    && !meshContains m ⟨10, 10⟩ && meshContains m ⟨-1.7, -1.7⟩ (opaqueOnly := true)
-- Dashing: on-runs fill, gaps stay empty.
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨20, 0⟩] false { width := 4, dash := some (#[6, 4], 0) }
  meshContains m ⟨3, 0⟩ (opaqueOnly := true) && !meshContains m ⟨8, 0⟩
    && meshContains m ⟨13, 0⟩ (opaqueOnly := true) && !meshContains m ⟨19.5, 0⟩
-- An invalid dash pattern (odd count) strokes solid.
#guard
  let m := outlineMesh #[⟨0, 0⟩, ⟨20, 0⟩] false { width := 4, dash := some (#[6], 0) }
  meshContains m ⟨8, 0⟩ (opaqueOnly := true)
-- Degenerates: zero width, single point, all-duplicate points.
#guard (strokeOutline #[⟨0, 0⟩, ⟨10, 0⟩] false { width := 0 }).isEmpty
#guard (strokeOutline #[⟨5, 5⟩] false { width := 4 }).isEmpty
#guard (strokeOutline #[⟨5, 5⟩, ⟨5, 5⟩, ⟨5, 5⟩] false { width := 4 }).isEmpty
-- pathStrokeMesh: well-formed, respects the boundsPad envelope.
#guard
  let p := Path.build (body := do
    PathM.moveTo ⟨5, 5⟩; PathM.lineTo ⟨40, 5⟩; PathM.quadTo ⟨50, 30⟩ ⟨20, 35⟩; PathM.close)
  let s : Stroke := { width := 5, join := .miter, cap := .square, dash := some (#[7, 3], 1) }
  let m := pathStrokeMesh p s .red
  m.indicesInRange &&
    (match m.bounds with
     | none => false
     | some b => (b.intersect (p.bounds.inflate s.boundsPad)) == b)

end Compose.Draw
