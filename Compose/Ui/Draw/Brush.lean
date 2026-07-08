import Compose.Core.Color
import Compose.Core.Geometry

/-!
# Brushes (`Compose/Ui/Draw/Brush.lean`)

Pure paint description evaluated per vertex. A `linearGradient` is essentially
free in our pipeline: the tessellator emits a vertex per silhouette point and
`Brush.colorAt` supplies each vertex's color, so the GPU/software rasterizer
interpolates the gradient across the triangles (Compose leans on Skia shaders;
we lean on per-vertex colors).

Mirrors `androidx.compose.ui.graphics.Brush`.
-/

namespace Compose.Draw
open Compose

/-- A paint: either a flat color or an axis-aligned linear gradient between two
endpoints. Mirrors `androidx.compose.ui.graphics.Brush`
(`SolidColor` / `LinearGradient`). -/
inductive Brush where
  /-- A flat, single color. Mirrors `SolidColor`. -/
  | solid (c : Color)
  /-- A linear gradient: `stops` are `(fraction, color)` pairs (fractions in
  `[0, 1]`, ascending) sampled along the segment from `start` to `stop`.
  Mirrors `Brush.linearGradient`. -/
  | linearGradient (stops : Array (Float32 × Color)) (start stop : Offset)
  deriving Repr, Inhabited

namespace Brush

/-- Convenience constructor for an evenly-spaced two-color gradient. -/
def horizontalGradient (c0 c1 : Color) (start stop : Offset) : Brush :=
  .linearGradient #[(0, c0), (1, c1)] start stop

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

/-- The color this brush paints at pixel `p`. For a solid brush the point is
irrelevant; for a linear gradient, `p` is projected onto the `start → stop`
axis and the normalized position samples the stop list. -/
def colorAt (b : Brush) (p : Offset) : Color :=
  match b with
  | .solid c => c
  | .linearGradient stops start stop =>
    let axis := stop - start
    let len2 := Offset.dot axis axis
    let t := if len2 <= 1e-9 then 0 else Offset.dot (p - start) axis / len2
    sampleStops stops t

/-- The dominant/first color, used where a single representative color is needed
(e.g. the `fillRect` fast path only accepts a solid brush; this is the fallback
for degenerate gradients). -/
def primaryColor (b : Brush) : Color :=
  match b with
  | .solid c => c
  | .linearGradient stops _ _ => if stops.isEmpty then .transparent else stops[0]!.2

/-- Whether this brush is a single flat color (enables the `fillRect` fast path). -/
def isSolid (b : Brush) : Bool :=
  match b with
  | .solid _ => true
  | .linearGradient .. => false

#guard (Brush.solid .red).colorAt ⟨5, 5⟩ == .red
#guard (Brush.solid .red).isSolid
#guard !(Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).isSolid
-- Gradient endpoints reproduce the stop colors.
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨0, 0⟩ == .black
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨10, 0⟩ == .white
-- Midpoint is the average.
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 0⟩ == Color.lerp .black .white 0.5
-- Clamps beyond the endpoints.
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨-5, 0⟩ == .black
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨20, 0⟩ == .white
-- Off-axis point projects onto the axis (only the along-axis component counts).
#guard (Brush.horizontalGradient .black .white ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 99⟩ == Color.lerp .black .white 0.5
-- Three-stop gradient samples the middle stop.
#guard (Brush.linearGradient #[(0, .red), (0.5, .green), (1, .blue)] ⟨0, 0⟩ ⟨10, 0⟩).colorAt ⟨5, 0⟩ == .green
-- Degenerate axis is constant (first stop).
#guard (Brush.linearGradient #[(0, .red), (1, .blue)] ⟨3, 3⟩ ⟨3, 3⟩).colorAt ⟨9, 9⟩ == .red
#guard (Brush.solid .cyan).primaryColor == .cyan

end Brush

end Compose.Draw
