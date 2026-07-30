module

public import Compose.Core.Color
public meta import Compose.Core.Color
public import Compose.Core.Geometry
public meta import Compose.Core.Geometry

public section

/-!
# Brushes (`Compose/Ui/Draw/Brush.lean`)

Pure paint description evaluated per vertex. Gradients are essentially free in
our pipeline: the tessellator emits a vertex per silhouette point and
`Brush.colorAt` supplies each vertex's color, so the GPU/software rasterizer
interpolates the gradient across the triangles (Compose leans on Skia shaders;
we lean on per-vertex colors). On the GPU backend, 2-stop gradients evaluate
exactly per fragment in the quad shader instead (`Gpu/Encode.quadBrush`); the
per-vertex form remains the SDL backend's documented fallback — coarse for
radial/sweep on shapes with few interior vertices (DESIGN.md).

Mirrors `androidx.compose.ui.graphics.Brush`.
-/

namespace Compose.Draw
open Compose

/-- A paint: a flat color or a linear/radial/sweep gradient. Mirrors
`androidx.compose.ui.graphics.Brush` (`SolidColor` / `LinearGradient` /
`RadialGradient` / `SweepGradient`). -/
inductive Brush where
  /-- A flat, single color. Mirrors `SolidColor`. -/
  | solid (c : Color)
  /-- A linear gradient: `stops` are `(fraction, color)` pairs (fractions in
  `[0, 1]`, ascending) sampled along the segment from `start` to `stop`.
  Mirrors `Brush.linearGradient`. -/
  | linearGradient (stops : Array (Float32 × Color)) (start stop : Offset)
  /-- A radial gradient: stops sampled by distance from `center`, normalized
  by `radius` (clamped at the rim). Mirrors `Brush.radialGradient`. -/
  | radialGradient (stops : Array (Float32 × Color)) (center : Offset) (radius : Float32)
  /-- A sweep (angular) gradient: stops sampled by the angle around `center`,
  measured clockwise in radians from the +x axis starting at `startAngle`
  (the fraction wraps — stop 0 and stop 1 meet at the seam). Mirrors
  `Brush.sweepGradient`. -/
  | sweepGradient (stops : Array (Float32 × Color)) (center : Offset) (startAngle : Float32 := 0)
  deriving Repr, BEq, Inhabited

namespace Brush

/-- Convenience constructor for an evenly-spaced two-color gradient along the
`start → stop` axis (any direction). Mirrors `Brush.linearGradient` with two
stops. -/
def gradient (c0 c1 : Color) (start stop : Offset) : Brush :=
  .linearGradient #[(0, c0), (1, c1)] start stop

/-- Convenience constructor for a two-color radial gradient (`c0` at `center`,
`c1` at the rim). -/
def radial (c0 c1 : Color) (center : Offset) (radius : Float32) : Brush :=
  .radialGradient #[(0, c0), (1, c1)] center radius

/-- Evaluate a sorted stop list at fraction `t ∈ [0, 1]`, linearly interpolating
between the bracketing stops (clamped at the ends). An empty stop list is
transparent; a single stop is constant. -/
private def sampleStops (stops : Array (Float32 × Color)) (t : Float32) : Color := Id.run do
  if stops.isEmpty then return .transparent
  let t := min 1 (max 0 t)
  if t <= stops[0]!.1 then return stops[0]!.2
  let last := stops[stops.size - 1]!
  if t >= last.1 then return last.2
  for i in [0:stops.size - 1] do
    let (f0, c0) := stops[i]!
    let (f1, c1) := stops[i + 1]!
    if t >= f0 && t <= f1 then
      let span := f1 - f0
      let frac := if span <= 1e-6 then 0 else (t - f0) / span
      return Color.lerp c0 c1 frac
  return last.2

/-- The color this brush paints at pixel `p`: linear projects onto the
`start → stop` axis, radial samples by normalized distance from the center,
sweep by the wrapped angle fraction around it (`atan2` via the `Float`
roundtrip — no native `Float32` trig; the GPU sweep shader is the twin,
`Gpu.Sdf.sweepT`). -/
def colorAt (b : Brush) (p : Offset) : Color :=
  match b with
  | .solid c => c
  | .linearGradient stops start stop =>
    let axis := stop - start
    let len2 := Offset.dot axis axis
    let t := if len2 <= 1e-9 then 0 else Offset.dot (p - start) axis / len2
    sampleStops stops t
  | .radialGradient stops center radius =>
    let t := if radius <= 1e-6 then 1 else p.distance center / radius
    sampleStops stops t
  | .sweepGradient stops center startAngle =>
    let d := p - center
    let ang := (Float.atan2 d.y.toFloat d.x.toFloat).toFloat32
    let twoPi : Float32 := 6.28318530717958647692
    let t := (ang - startAngle) / twoPi
    sampleStops stops (t - t.floor)

/-- The dominant/first color, used where a single representative color is needed
(e.g. the `fillRect` fast path only accepts a solid brush; this is the fallback
for degenerate gradients). -/
def primaryColor (b : Brush) : Color :=
  match b with
  | .solid c => c
  | .linearGradient stops _ _ | .radialGradient stops _ _ | .sweepGradient stops _ _ =>
    if stops.isEmpty then .transparent else stops[0]!.2

/-- Whether this brush is a single flat color (enables the `fillRect` fast path). -/
def isSolid (b : Brush) : Bool :=
  match b with
  | .solid _ => true
  | _ => false

/-- Map a **unit-space** brush onto a `size`-px box: points scale per axis
(`⟨0.5, 1⟩` → bottom center), a radial radius by the larger dimension (so a
unit radius from a corner reaches across a wide panel), angles unchanged.
Theme-level brushes (`GlassSpec`) are unit-space and scaled here at draw
time, keeping the recorded `DrawElem`/`ShapeSpec` structurally comparable
per element size. Solid brushes are unaffected. -/
def scaleTo (b : Brush) (size : Size) : Brush :=
  let pt (p : Offset) : Offset := ⟨p.x * size.width, p.y * size.height⟩
  match b with
  | .solid c => .solid c
  | .linearGradient stops start stop => .linearGradient stops (pt start) (pt stop)
  | .radialGradient stops center radius =>
    .radialGradient stops (pt center) (radius * max size.width size.height)
  | .sweepGradient stops center startAngle => .sweepGradient stops (pt center) startAngle

#guard (Brush.solid .red).colorAt ⟨5, 5⟩ == .red
#guard (Brush.solid .red).isSolid
#guard !(Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).isSolid
-- Gradient endpoints reproduce the stop colors.
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨0, 0⟩ == .black
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨10, 0⟩ == .white
-- Midpoint is the average.
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 0⟩ == Color.lerp .black .white 0.5
-- Clamps beyond the endpoints.
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨-5, 0⟩ == .black
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨20, 0⟩ == .white
-- Off-axis point projects onto the axis (only the along-axis component counts).
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 99⟩ == Color.lerp .black .white 0.5
-- Three-stop gradient samples the middle stop.
#guard (Brush.linearGradient #[(0, .red), (0.5, .green), (1, .blue)] ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 0⟩ == .green
-- Degenerate axis is constant (first stop).
#guard (Brush.linearGradient #[(0, .red), (1, .blue)] ⟨3, 3⟩ ⟨3, 3⟩).colorAt ⟨9, 9⟩ == .red
#guard (Brush.solid .cyan).primaryColor == .cyan
-- Radial: center is the first stop, the rim the last, clamped beyond it.
#guard (Brush.radial .red .blue ⟨50, 50⟩ 10).colorAt ⟨50, 50⟩ == .red
#guard (Brush.radial .red .blue ⟨50, 50⟩ 10).colorAt ⟨60, 50⟩ == .blue
#guard (Brush.radial .red .blue ⟨50, 50⟩ 10).colorAt ⟨50, 99⟩ == .blue
#guard (Brush.radial .black .white ⟨50, 50⟩ 10).colorAt ⟨50, 45⟩ == Color.lerp .black .white 0.5
-- Distance is Euclidean: a 3-4-5 triangle lands at t = 0.5 on radius 10.
#guard (Brush.radial .black .white ⟨0, 0⟩ 10).colorAt ⟨3, 4⟩ == Color.lerp .black .white 0.5
-- Degenerate radius paints the last stop.
#guard (Brush.radial .red .blue ⟨0, 0⟩ 0).colorAt ⟨5, 5⟩ == .blue
#guard !(Brush.radial .red .blue ⟨0, 0⟩ 10).isSolid
#guard (Brush.radial .red .blue ⟨0, 0⟩ 10).primaryColor == .red
-- Sweep: t = 0 on the +x axis, 0.25 straight down (screen y grows down),
-- 0.5 on the −x axis, 0.75 straight up.
#guard (Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨50, 50⟩).colorAt ⟨60, 50⟩ == .red
#guard
  let b := Brush.sweepGradient #[(0, Color.black), (1, .white)] ⟨50, 50⟩
  (b.colorAt ⟨50, 60⟩ == Color.lerp .black .white 0.25)
    && (b.colorAt ⟨40, 50⟩ == Color.lerp .black .white 0.5)
    && (b.colorAt ⟨50, 40⟩ == Color.lerp .black .white 0.75)
-- `startAngle` rotates the seam: a quarter-turn start puts t = 0 straight down.
#guard
  let quarter : Float32 := 1.57079632679489661923
  (Brush.sweepGradient #[(0, Color.red), (1, .blue)] ⟨50, 50⟩ quarter).colorAt ⟨50, 60⟩ == .red
-- The fraction wraps: 2π beyond the start angle is the start again (seam
-- continuity — approaching from below the +x axis lands near t = 1).
#guard
  let b := Brush.sweepGradient #[(0, Color.black), (1, .white)] ⟨0, 0⟩
  let below := b.colorAt ⟨100, -0.01⟩
  (below.r - 1).abs < 0.01 && ((b.colorAt ⟨100, 0.01⟩).r < 0.01)
#guard !(Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨0, 0⟩).isSolid
#guard (Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨0, 0⟩).primaryColor == .red
-- scaleTo: solids are untouched; gradient points scale per axis.
#guard (Brush.solid .red).scaleTo ⟨40, 20⟩ == .solid .red
#guard (Brush.gradient .black .white ⟨0, 0⟩ ⟨1, 1⟩).scaleTo ⟨40, 20⟩
        == Brush.gradient .black .white ⟨0, 0⟩ ⟨40, 20⟩
-- A vertical unit gradient spans the box height regardless of width.
#guard (Brush.gradient .black .white ⟨0.5, 0⟩ ⟨0.5, 1⟩).scaleTo ⟨40, 20⟩
        == Brush.gradient .black .white ⟨20, 0⟩ ⟨20, 20⟩
-- Radial: center scales per axis, the radius by the larger dimension.
#guard (Brush.radial .red .blue ⟨0.5, 0.5⟩ 0.5).scaleTo ⟨40, 20⟩
        == Brush.radial .red .blue ⟨20, 10⟩ 20
-- Sweep: center scales, the start angle is untouched.
#guard (Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨0.5, 1⟩ 2).scaleTo ⟨40, 20⟩
        == Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨20, 20⟩ 2

end Brush

end Compose.Draw

end
