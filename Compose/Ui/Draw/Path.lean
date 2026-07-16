module

public import Compose.Core.Geometry
public meta import Compose.Core.Geometry

public section

/-!
# Vector paths (`Compose/Ui/Draw/Path.lean`)

The pure path model: a `Path` is an array of absolute-coordinate `PathVerb`s
plus a `FillRule`, built with the `Path.build` monadic builder (which tracks
the current point for relative ops and lowers arcs to cubics — arcs are not a
verb). Everything downstream consumes paths through two total functions:
`Path.flatten` (adaptive de Casteljau subdivision to polygonal contours, used
by the band-sweep fill tessellator in `PathFill.lean`) and `Path.windingAt` /
`Path.contains` (the exact geometric oracle for tests and feather-side
classification). No SDL, no `IO`.

Mirrors `androidx.compose.ui.graphics.Path`, shrunk to Lean idioms: an
immutable verb array + a `StateM` builder instead of a mutable object. SVG
path parsing is a later icons capability; it will lower into these verbs.
-/

namespace Compose.Draw
open Compose

/-- π as a `Float32` (Lean's stdlib has no `Float.pi`). -/
private def piF : Float32 := 3.14159265358979323846

/-- One path segment, in absolute pixel coordinates. Curves carry their control
points; arcs lower to `cubicTo` at build time. Mirrors the verb set of
`android.graphics.Path` / Skia's `SkPathVerb`. -/
inductive PathVerb where
  /-- Start a new subpath at `p`. -/
  | moveTo (p : Offset)
  /-- Straight segment from the current point to `p`. -/
  | lineTo (p : Offset)
  /-- Quadratic Bézier with control `c`, ending at `p`. -/
  | quadTo (c p : Offset)
  /-- Cubic Bézier with controls `c1`, `c2`, ending at `p`. -/
  | cubicTo (c1 c2 p : Offset)
  /-- Close the current subpath back to its start. -/
  | close
  deriving Repr, BEq, Inhabited

/-- The points a verb mentions (controls included) — the input of the
control-point bounds hull. -/
def PathVerb.points : PathVerb → Array Offset
  | .moveTo p => #[p]
  | .lineTo p => #[p]
  | .quadTo c p => #[c, p]
  | .cubicTo c1 c2 p => #[c1, c2, p]
  | .close => #[]

/-- The verb displaced by `d` (all points, controls included). -/
def PathVerb.translate (v : PathVerb) (d : Offset) : PathVerb :=
  match v with
  | .moveTo p => .moveTo (p + d)
  | .lineTo p => .lineTo (p + d)
  | .quadTo c p => .quadTo (c + d) (p + d)
  | .cubicTo c1 c2 p => .cubicTo (c1 + d) (c2 + d) (p + d)
  | .close => .close

/-- How winding numbers classify interior points. Mirrors
`androidx.compose.ui.graphics.PathFillType`. -/
inductive FillRule where
  /-- Inside where the winding number is non-zero (the default). -/
  | nonZero
  /-- Inside where the winding number is odd. -/
  | evenOdd
  deriving Repr, BEq, Inhabited

/-- Whether winding number `w` is inside under this rule. -/
def FillRule.isInside (rule : FillRule) (w : Int) : Bool :=
  match rule with
  | .nonZero => w != 0
  | .evenOdd => w % 2 != 0

#guard FillRule.nonZero.isInside 2 && !FillRule.evenOdd.isInside 2
#guard FillRule.nonZero.isInside (-1) && FillRule.evenOdd.isInside (-1)
#guard !FillRule.nonZero.isInside 0 && !FillRule.evenOdd.isInside 0

/-- An arbitrary vector path: absolute-coordinate verbs plus the fill rule.
Value equality (`BEq`) is verb-array equality — a `ShapeSpec` carrying a path
stays a valid mesh-cache key. Mirrors `androidx.compose.ui.graphics.Path`. -/
structure Path where
  verbs : Array PathVerb := #[]
  fillRule : FillRule := .nonZero
  deriving Repr, BEq, Inhabited

/-- The path displaced by `d` — how the recorder moves an ambient clip path
between coordinate frames (`DrawScope.clipPath`). -/
def Path.translate (path : Path) (d : Offset) : Path :=
  { path with verbs := path.verbs.map (·.translate d) }

/-- The verb with all points scaled by `f` about the origin. -/
def PathVerb.scale (f : Float32) : PathVerb → PathVerb
  | .moveTo p => .moveTo (p * f)
  | .lineTo p => .lineTo (p * f)
  | .quadTo c p => .quadTo (c * f) (p * f)
  | .cubicTo c1 c2 p => .cubicTo (c1 * f) (c2 * f) (p * f)
  | .close => .close

/-- The path scaled uniformly by `f` about the origin — how a vector asset
authored in viewport units stretches to its drawn pixel size. -/
def Path.scale (path : Path) (f : Float32) : Path :=
  { path with verbs := path.verbs.map (·.scale f) }

#guard (Path.mk #[.lineTo ⟨2, 3⟩] .nonZero).scale 2 == Path.mk #[.lineTo ⟨4, 6⟩] .nonZero

/-! ## Builder -/

/-- Builder state: the verbs so far, the current point, the current subpath's
start (for `close` and post-`close` continuation), and whether a subpath is
open. -/
structure PathBuilder where
  verbs : Array PathVerb := #[]
  current : Offset := .zero
  start : Offset := .zero
  inSubpath : Bool := false

/-- The path-building monad: state over `PathBuilder`. -/
abbrev PathM := StateM PathBuilder

namespace PathM

/-- Start a new subpath at `p`. -/
def moveTo (p : Offset) : PathM Unit :=
  modify fun b => { verbs := b.verbs.push (.moveTo p), current := p, start := p, inSubpath := true }

/-- Open a subpath at the current point if none is open (Skia's implicit
`moveTo` for a leading `lineTo`, and continuation after `close`). -/
private def ensureStart : PathM Unit := do
  if !(← get).inSubpath then moveTo (← get).current

/-- Straight segment to `p`. -/
def lineTo (p : Offset) : PathM Unit := do
  ensureStart
  modify fun b => { b with verbs := b.verbs.push (.lineTo p), current := p }

/-- Quadratic Bézier through control `c` to `p`. -/
def quadTo (c p : Offset) : PathM Unit := do
  ensureStart
  modify fun b => { b with verbs := b.verbs.push (.quadTo c p), current := p }

/-- Cubic Bézier through controls `c1`, `c2` to `p`. -/
def cubicTo (c1 c2 p : Offset) : PathM Unit := do
  ensureStart
  modify fun b => { b with verbs := b.verbs.push (.cubicTo c1 c2 p), current := p }

/-- Close the current subpath (no-op when none is open); the current point
returns to the subpath start. -/
def close : PathM Unit := do
  if (← get).inSubpath then
    modify fun b =>
      { b with verbs := b.verbs.push .close, current := b.start, inSubpath := false }

/-- `moveTo` displaced from the current point. -/
def relMoveTo (d : Offset) : PathM Unit := do moveTo ((← get).current + d)

/-- `lineTo` displaced from the current point. -/
def relLineTo (d : Offset) : PathM Unit := do lineTo ((← get).current + d)

/-- `quadTo` with control and end displaced from the current point. -/
def relQuadTo (dc dp : Offset) : PathM Unit := do
  let cur := (← get).current
  quadTo (cur + dc) (cur + dp)

/-- `cubicTo` with controls and end displaced from the current point. -/
def relCubicTo (dc1 dc2 dp : Offset) : PathM Unit := do
  let cur := (← get).current
  cubicTo (cur + dc1) (cur + dc2) (cur + dp)

/-- Point on the axis-aligned ellipse centered at `c` with radii `rx`/`ry` at
angle `a` (radians, y-down screen convention). -/
private def ellipseAt (c : Offset) (rx ry : Float32) (a : Float32) : Offset :=
  ⟨c.x + rx * (Float.cos a.toFloat).toFloat32, c.y + ry * (Float.sin a.toFloat).toFloat32⟩

/-- Append an elliptical arc about `center` with radii `rx`/`ry` from angle
`startRad` sweeping `sweepRad` radians (y-down convention: positive sweep is
clockwise on screen). Lowers to cubic Béziers in ≤ 90° segments with the
standard tangent-length factor `k = 4/3 · tan(θ/4)` — arcs are not a verb. An
open subpath gains a straight segment to the arc's start; otherwise the arc
starts a new subpath. Zero radii degrade to a segment to `center`. -/
def arcTo (center : Offset) (rx ry : Float32) (startRad sweepRad : Float32) : PathM Unit := do
  let startOrLine (p : Offset) : PathM Unit := do
    let b ← get
    if b.inSubpath then
      if b.current != p then lineTo p
    else moveTo p
  if rx <= 1e-6 && ry <= 1e-6 then
    startOrLine center
  else
    startOrLine (ellipseAt center rx ry startRad)
    if sweepRad.abs > 1e-6 then
      let segs := max 1 ((sweepRad.abs / (piF / 2)).toFloat.ceil.toUInt64.toNat)
      let step := sweepRad / segs.toFloat32
      let k := (4.0 / 3.0 * Float.tan (step.toFloat / 4)).toFloat32
      -- derivative of the ellipse point w.r.t. the angle
      let deriv (a : Float32) : Offset :=
        ⟨-rx * (Float.sin a.toFloat).toFloat32, ry * (Float.cos a.toFloat).toFloat32⟩
      for i in [0:segs] do
        let a0 := startRad + step * i.toFloat32
        let a1 := a0 + step
        let p0 := ellipseAt center rx ry a0
        let p1 := ellipseAt center rx ry a1
        cubicTo (p0 + deriv a0 * k) (p1 - deriv a1 * k) p1

/-- Append `r` as a closed clockwise subpath. -/
def addRect (r : Rect) : PathM Unit := do
  if r.isEmpty then return
  moveTo ⟨r.left, r.top⟩
  lineTo ⟨r.right, r.top⟩
  lineTo ⟨r.right, r.bottom⟩
  lineTo ⟨r.left, r.bottom⟩
  close

/-- Append the ellipse inscribed in `r` as a closed clockwise subpath. -/
def addOval (r : Rect) : PathM Unit := do
  if r.isEmpty then return
  let c := r.center
  moveTo ⟨r.right, c.y⟩
  arcTo c (r.width / 2) (r.height / 2) 0 (2 * piF)
  close

/-- Append a rounded rect (radii normalized first) as a closed clockwise
subpath; the straight edges come from `arcTo`'s connecting segments. -/
def addRoundRect (rr : RoundRect) : PathM Unit := do
  if rr.rect.isEmpty then return
  let rr := rr.normalize
  let r := rr.rect
  moveTo ⟨r.left, r.top + rr.topLeft.y⟩
  arcTo ⟨r.left + rr.topLeft.x, r.top + rr.topLeft.y⟩ rr.topLeft.x rr.topLeft.y piF (piF / 2)
  arcTo ⟨r.right - rr.topRight.x, r.top + rr.topRight.y⟩ rr.topRight.x rr.topRight.y
    (piF * 1.5) (piF / 2)
  arcTo ⟨r.right - rr.bottomRight.x, r.bottom - rr.bottomRight.y⟩ rr.bottomRight.x
    rr.bottomRight.y 0 (piF / 2)
  arcTo ⟨r.left + rr.bottomLeft.x, r.bottom - rr.bottomLeft.y⟩ rr.bottomLeft.x rr.bottomLeft.y
    (piF / 2) (piF / 2)
  close

end PathM

/-- Run a builder block into a `Path`:
`Path.build do moveTo p; lineTo q; close` (with `open PathM`), or
`Path.build (fillRule := .evenOdd) do …`. -/
def Path.build (body : PathM Unit) (fillRule : FillRule := .nonZero) : Path :=
  { verbs := (body.run {}).2.verbs, fillRule }

/-! ## Bounds -/

/-- Conservative bounds: the hull of every on-curve and control point (cheap;
curves never escape their control hull). The empty path is `Rect.zero`. -/
def Path.bounds (path : Path) : Rect := Id.run do
  let mut acc : Option Rect := none
  for v in path.verbs do
    for p in v.points do
      acc := some (match acc with
        | none => ⟨p.x, p.y, p.x, p.y⟩
        | some r => ⟨min r.left p.x, min r.top p.y, max r.right p.x, max r.bottom p.y⟩)
  return acc.getD .zero

/-! ## Flattening -/

/-- Adaptive quadratic subdivision: append the curve's polyline (excluding the
start point, ending exactly at `p1`) while the control's chord distance
exceeds `tol`; `fuel` caps the depth. -/
private def flatQuadAux : Nat → Offset → Offset → Offset → Float32 → Array Offset → Array Offset
  | 0, _, _, p1, _, acc => acc.push p1
  | fuel + 1, p0, c, p1, tol, acc =>
    if Offset.distToSegment c p0 p1 <= tol then acc.push p1
    else
      let a := Offset.lerp p0 c 0.5
      let b := Offset.lerp c p1 0.5
      let m := Offset.lerp a b 0.5
      flatQuadAux fuel m b p1 tol (flatQuadAux fuel p0 a m tol acc)

/-- Adaptive cubic subdivision (de Casteljau split at ½), same contract as
`flatQuadAux`. -/
private def flatCubicAux :
    Nat → Offset → Offset → Offset → Offset → Float32 → Array Offset → Array Offset
  | 0, _, _, _, p1, _, acc => acc.push p1
  | fuel + 1, p0, c1, c2, p1, tol, acc =>
    if max (Offset.distToSegment c1 p0 p1) (Offset.distToSegment c2 p0 p1) <= tol then
      acc.push p1
    else
      let p01 := Offset.lerp p0 c1 0.5
      let p12 := Offset.lerp c1 c2 0.5
      let p23 := Offset.lerp c2 p1 0.5
      let a := Offset.lerp p01 p12 0.5
      let b := Offset.lerp p12 p23 0.5
      let m := Offset.lerp a b 0.5
      flatCubicAux fuel m b p23 p1 tol (flatCubicAux fuel p0 p01 a m tol acc)

/-- Subdivision depth cap (2¹⁶ segments per curve is far past any tol). -/
private def flattenFuel : Nat := 16

/-- Flatten to polygonal contours: each is the subpath's points in order plus
whether it was explicitly closed (fill treats every contour as closed; the
flag matters for stroking). Curves subdivide adaptively until the control
points sit within `tol` device pixels of the chord (depth-capped).
Single-point subpaths are dropped. -/
def Path.flatten (path : Path) (tol : Float32 := 0.25) : Array (Array Offset × Bool) := Id.run do
  let mut out : Array (Array Offset × Bool) := #[]
  let mut cur : Array Offset := #[]
  let mut pos : Offset := .zero
  let flush (cur : Array Offset) (closed : Bool) (out : Array (Array Offset × Bool)) :=
    if cur.size >= 2 then out.push (cur, closed) else out
  for v in path.verbs do
    match v with
    | .moveTo p =>
      out := flush cur false out
      cur := #[p]
      pos := p
    | .lineTo p =>
      if cur.isEmpty then cur := #[pos]
      cur := cur.push p
      pos := p
    | .quadTo c p =>
      if cur.isEmpty then cur := #[pos]
      cur := flatQuadAux flattenFuel pos c p tol cur
      pos := p
    | .cubicTo c1 c2 p =>
      if cur.isEmpty then cur := #[pos]
      cur := flatCubicAux flattenFuel pos c1 c2 p tol cur
      pos := p
    | .close =>
      pos := cur[0]?.getD pos
      out := flush cur true out
      cur := #[]
  return flush cur false out

/-! ## Winding -/

/-- Winding number of `p` against closed polygonal contours: signed crossings
of the rightward horizontal ray, `+1` per downward edge (so a clockwise
contour in y-down screen coordinates winds `+1` around its interior). The
half-open vertical rule (`≤` on both ends) counts each vertex exactly once. -/
def polyWinding (contours : Array (Array Offset)) (p : Offset) : Int := Id.run do
  let mut w : Int := 0
  for pts in contours do
    let n := pts.size
    for i in [0:n] do
      let a := pts[i]!
      let b := pts[(i + 1) % n]!
      if (a.y <= p.y) != (b.y <= p.y) then
        let t := (p.y - a.y) / (b.y - a.y)
        if a.x + t * (b.x - a.x) > p.x then
          w := w + (if b.y > a.y then 1 else -1)
  return w

/-- Winding number of `p` (contours flattened at `tol`, all treated closed) —
the geometric reference the fill tessellator is tested against. -/
def Path.windingAt (path : Path) (p : Offset) (tol : Float32 := 0.25) : Int :=
  polyWinding ((path.flatten tol).map (·.1)) p

/-- Whether `p` is inside the path under its fill rule (the test oracle; also
the eventual `clipPath` hit-test). -/
def Path.contains (path : Path) (p : Offset) (tol : Float32 := 0.25) : Bool :=
  path.fillRule.isInside (path.windingAt p tol)

/-! ## `#guard` tests -/

private def approxOff (a b : Offset) (tol : Float32 := 0.05) : Bool :=
  (a.x - b.x).abs <= tol && (a.y - b.y).abs <= tol

section
open PathM

-- Builder semantics: verbs recorded in order; close returns to the subpath
-- start; a leading lineTo opens a subpath at the origin; rel ops are
-- current-point relative.
#guard (Path.build do moveTo ⟨1, 2⟩; lineTo ⟨3, 4⟩; close).verbs
        == #[.moveTo ⟨1, 2⟩, .lineTo ⟨3, 4⟩, .close]
#guard (Path.build do lineTo ⟨3, 4⟩).verbs == #[.moveTo ⟨0, 0⟩, .lineTo ⟨3, 4⟩]
#guard (Path.build do moveTo ⟨1, 1⟩; lineTo ⟨5, 1⟩; close; lineTo ⟨1, 5⟩).verbs
        == #[.moveTo ⟨1, 1⟩, .lineTo ⟨5, 1⟩, .close, .moveTo ⟨1, 1⟩, .lineTo ⟨1, 5⟩]
#guard (Path.build do moveTo ⟨10, 10⟩; relLineTo ⟨5, 0⟩; relLineTo ⟨0, 5⟩).verbs
        == #[.moveTo ⟨10, 10⟩, .lineTo ⟨15, 10⟩, .lineTo ⟨15, 15⟩]
#guard (Path.build do moveTo ⟨10, 10⟩; relQuadTo ⟨5, 0⟩ ⟨5, 5⟩).verbs
        == #[.moveTo ⟨10, 10⟩, .quadTo ⟨15, 10⟩ ⟨15, 15⟩]
#guard (Path.build (fillRule := .evenOdd) do moveTo ⟨0, 0⟩).fillRule == .evenOdd

#guard (Path.build do addRect ⟨1, 2, 5, 6⟩).verbs
        == #[.moveTo ⟨1, 2⟩, .lineTo ⟨5, 2⟩, .lineTo ⟨5, 6⟩, .lineTo ⟨1, 6⟩, .close]
#guard (Path.build do PathM.addRect ⟨5, 5, 5, 9⟩).verbs.isEmpty   -- empty rect: no verbs

-- arcTo endpoints land on the ellipse; a quarter arc is one cubic.
#guard
  let p := Path.build do arcTo ⟨0, 0⟩ 10 10 0 (piF / 2)
  p.verbs.size == 2 &&
    (match p.verbs[0]!, p.verbs[1]! with
     | .moveTo s, .cubicTo _ _ e => approxOff s ⟨10, 0⟩ && approxOff e ⟨0, 10⟩
     | _, _ => false)

-- An oval's flattened points stay within curve-approximation error of the
-- circle, and segment midpoints within the flatten tol of it (the adaptive
-- subdivision actually subdivides).
#guard
  let pts := ((Path.build do addOval ⟨0, 0, 40, 40⟩).flatten).flatMap (·.1)
  pts.size > 8 && pts.all fun p => (Offset.distance p ⟨20, 20⟩ - 20).abs < 0.05
#guard
  let pts := ((Path.build do addOval ⟨0, 0, 40, 40⟩).flatten)[0]!.1
  (Array.range pts.size).all fun i =>
    let m := Offset.lerp pts[i]! pts[(i + 1) % pts.size]! 0.5
    (Offset.distance m ⟨20, 20⟩ - 20).abs < 0.3

-- Bounds: control-point hull (the quad control sticks out).
#guard (Path.build do moveTo ⟨1, 2⟩; lineTo ⟨5, 6⟩).bounds == (⟨1, 2, 5, 6⟩ : Rect)
#guard (Path.build do moveTo ⟨0, 10⟩; quadTo ⟨10, -10⟩ ⟨20, 10⟩).bounds
        == (⟨0, -10, 20, 10⟩ : Rect)
#guard (Path.mk #[] .nonZero).bounds == Rect.zero

-- Translate displaces every point (controls included) and keeps the rule.
#guard (Path.build (fillRule := .evenOdd) do
          moveTo ⟨1, 2⟩; quadTo ⟨3, 4⟩ ⟨5, 6⟩; close).translate ⟨10, 20⟩
        == Path.build (fillRule := .evenOdd) do
          moveTo ⟨11, 22⟩; quadTo ⟨13, 24⟩ ⟨15, 26⟩; close
#guard ((Path.build do addRect ⟨0, 0, 10, 10⟩).translate ⟨5, 5⟩).bounds == (⟨5, 5, 15, 15⟩ : Rect)

-- Flatten: lines pass through; close marks the contour; single points drop.
#guard (Path.build do moveTo ⟨0, 0⟩; lineTo ⟨4, 0⟩; lineTo ⟨4, 4⟩; close).flatten
        == #[(#[⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 4⟩], true)]
#guard (Path.build do moveTo ⟨0, 0⟩; lineTo ⟨4, 0⟩; moveTo ⟨9, 9⟩).flatten
        == #[(#[⟨0, 0⟩, ⟨4, 0⟩], false)]

-- Winding: clockwise square winds +1; nested reversed square carves a hole;
-- the even-odd rule sees the hole regardless of the inner winding.
#guard (Path.build do addRect ⟨0, 0, 10, 10⟩).windingAt ⟨5, 5⟩ == 1
#guard (Path.build do addRect ⟨0, 0, 10, 10⟩).windingAt ⟨15, 5⟩ == 0
#guard
  let donut := Path.build do
    addRect ⟨0, 0, 30, 30⟩
    -- reversed (counter-clockwise) inner square
    moveTo ⟨10, 10⟩; lineTo ⟨10, 20⟩; lineTo ⟨20, 20⟩; lineTo ⟨20, 10⟩; close
  donut.windingAt ⟨5, 15⟩ == 1 && donut.windingAt ⟨15, 15⟩ == 0
    && donut.contains ⟨5, 15⟩ && !donut.contains ⟨15, 15⟩
#guard
  let rings := Path.build (fillRule := .evenOdd) do
    addRect ⟨0, 0, 30, 30⟩
    addRect ⟨10, 10, 20, 20⟩   -- same winding; even-odd still carves it out
  rings.windingAt ⟨15, 15⟩ == 2 && !rings.contains ⟨15, 15⟩ && rings.contains ⟨5, 15⟩

end

end Compose.Draw

end
