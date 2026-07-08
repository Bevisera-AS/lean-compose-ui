import Compose.Core.Color
import Compose.Core.Geometry
import Compose.Core.Density

namespace Compose

/-!
# Animation vectors (`Compose/Animation/Vector.lean`)

Every animatable type is converted to a small vector of `Float32` dimensions
that specs animate independently, mirroring
`androidx.compose.animation.core.AnimationVector1D..4D` +
`TwoWayConverter`. A single array-backed struct covers all arities (the
per-dimension operations are uniform, which is what the spec evaluators
need).

**Documented deviation:** `VectorConverter.color` animates in non-premultiplied
sRGB channels (Compose converts through Oklab by default); channels are
clamped to `[0, 1]` on the way back so over/undershooting springs stay valid
colors.
-/

/-- A 1–4 dimensional vector of animatable `Float32` values. Mirrors
`androidx.compose.animation.core.AnimationVector`. -/
structure AnimationVector where
  values : Array Float32
  deriving Repr, BEq, Inhabited

namespace AnimationVector

/-- 1D vector. Mirrors `AnimationVector1D`. -/
def v1 (a : Float32) : AnimationVector := ⟨#[a]⟩

/-- 2D vector. Mirrors `AnimationVector2D`. -/
def v2 (a b : Float32) : AnimationVector := ⟨#[a, b]⟩

/-- 3D vector. Mirrors `AnimationVector3D`. -/
def v3 (a b c : Float32) : AnimationVector := ⟨#[a, b, c]⟩

/-- 4D vector. Mirrors `AnimationVector4D`. -/
def v4 (a b c d : Float32) : AnimationVector := ⟨#[a, b, c, d]⟩

/-- Number of dimensions. Mirrors `AnimationVector.size`. -/
def dim (v : AnimationVector) : Nat := v.values.size

/-- The zero vector of `n` dimensions. Mirrors `newVector()`/`reset()`. -/
def zero (n : Nat) : AnimationVector := ⟨.replicate n 0.0⟩

/-- Dimension `i` (`0` out of range). Mirrors `AnimationVector.get`. -/
def get (v : AnimationVector) (i : Nat) : Float32 := v.values.getD i 0.0

/-- Apply `f` to every dimension. -/
def map (f : Float32 → Float32) (v : AnimationVector) : AnimationVector :=
  ⟨v.values.map f⟩

/-- Combine two vectors dimension-wise (`b` read with `get`, so a dimension
mismatch pads with `0`). -/
def zipWith (f : Float32 → Float32 → Float32) (a b : AnimationVector) :
    AnimationVector :=
  ⟨a.values.mapIdx fun i x => f x (b.get i)⟩

/-- Dimension-wise linear interpolation (`t` unclamped: springs and easings
may overshoot). -/
def lerp (a b : AnimationVector) (t : Float32) : AnimationVector :=
  zipWith (fun x y => x + (y - x) * t) a b

/-- Whether `p` holds in every dimension of the zipped pair. -/
def all2 (p : Float32 → Float32 → Bool) (a b : AnimationVector) : Bool :=
  (List.range a.dim).all fun i => p (a.get i) (b.get i)

#guard (v2 1 2).dim == 2
#guard (v3 1 2 3).get 1 == 2
#guard (v1 5).get 3 == 0
#guard zero 4 == v4 0 0 0 0
#guard lerp (v2 0 10) (v2 10 20) 0.5 == v2 5 15
#guard lerp (v1 0) (v1 10) 1.5 == v1 15        -- overshoot allowed
#guard zipWith (· + ·) (v2 1 2) (v2 10 20) == v2 11 22
#guard all2 (· < ·) (v2 1 2) (v2 3 4)
#guard !all2 (· < ·) (v2 1 5) (v2 3 4)

end AnimationVector

/-- Bidirectional conversion between an animatable type and its
`AnimationVector`. Mirrors
`androidx.compose.animation.core.TwoWayConverter`. -/
structure VectorConverter (α : Type) where
  toVector : α → AnimationVector
  fromVector : AnimationVector → α

instance [Nonempty α] : Nonempty (VectorConverter α) :=
  ⟨{ toVector := fun _ => .v1 0, fromVector := fun _ => Classical.choice ‹_› }⟩

namespace VectorConverter

/-- Round to nearest, ties up — Kotlin's `roundToInt`, used when converting
vectors back to integer geometry. -/
private def roundToInt32 (x : Float32) : Int32 := (x + 0.5).floor.toInt32

private def clamp01 (v : Float32) : Float32 := min 1.0 (max 0.0 v)

/-- `Float32 ↔ 1D`. Mirrors `Float.Companion.VectorConverter`. -/
def float32 : VectorConverter Float32 :=
  { toVector := .v1, fromVector := (·.get 0) }

/-- `Dp ↔ 1D`. Mirrors `Dp.Companion.VectorConverter`. -/
def dp : VectorConverter Dp :=
  { toVector := fun d => .v1 d.value, fromVector := fun v => ⟨v.get 0⟩ }

/-- `Sp ↔ 1D`. Mirrors `TextUnit.Companion.VectorConverter` (sp only). -/
def sp : VectorConverter Sp :=
  { toVector := fun s => .v1 s.value, fromVector := fun v => ⟨v.get 0⟩ }

/-- `Offset ↔ 2D`. Mirrors `Offset.Companion.VectorConverter`. -/
def offset : VectorConverter Offset :=
  { toVector := fun o => .v2 o.x o.y, fromVector := fun v => ⟨v.get 0, v.get 1⟩ }

/-- `Size ↔ 2D`. Mirrors `Size.Companion.VectorConverter`. -/
def size : VectorConverter Size :=
  { toVector := fun s => .v2 s.width s.height
    fromVector := fun v => ⟨v.get 0, v.get 1⟩ }

/-- `IntOffset ↔ 2D` (rounded back). Mirrors
`IntOffset.Companion.VectorConverter`. -/
def intOffset : VectorConverter IntOffset :=
  { toVector := fun o => .v2 o.x.toFloat32 o.y.toFloat32
    fromVector := fun v => ⟨roundToInt32 (v.get 0), roundToInt32 (v.get 1)⟩ }

/-- `IntSize ↔ 2D` (rounded back). Mirrors
`IntSize.Companion.VectorConverter`. -/
def intSize : VectorConverter IntSize :=
  { toVector := fun s => .v2 s.width.toFloat32 s.height.toFloat32
    fromVector := fun v => ⟨roundToInt32 (v.get 0), roundToInt32 (v.get 1)⟩ }

/-- `Rect ↔ 4D`. Mirrors `Rect.Companion.VectorConverter`. -/
def rect : VectorConverter Rect :=
  { toVector := fun r => .v4 r.left r.top r.right r.bottom
    fromVector := fun v => ⟨v.get 0, v.get 1, v.get 2, v.get 3⟩ }

/-- `Color ↔ 4D` as `(r, g, b, a)` in sRGB, channels clamped on conversion
back. Mirrors `Color.Companion.VectorConverter` **except** the color space:
we interpolate raw sRGB channels where Compose converts through Oklab
(documented deviation — see the module docstring). -/
def color : VectorConverter Color :=
  { toVector := fun c => .v4 c.r c.g c.b c.a
    fromVector := fun v =>
      { r := clamp01 (v.get 0), g := clamp01 (v.get 1)
        b := clamp01 (v.get 2), a := clamp01 (v.get 3) } }

-- roundtrips
#guard float32.fromVector (float32.toVector 1.5) == 1.5
#guard dp.fromVector (dp.toVector 16) == (16 : Dp)
#guard sp.fromVector (sp.toVector 14) == (14 : Sp)
#guard offset.fromVector (offset.toVector ⟨3, 4⟩) == (⟨3, 4⟩ : Offset)
#guard size.fromVector (size.toVector ⟨30, 40⟩) == (⟨30, 40⟩ : Size)
#guard intOffset.fromVector (intOffset.toVector ⟨-3, 4⟩) == (⟨-3, 4⟩ : IntOffset)
#guard intSize.fromVector (intSize.toVector ⟨7, 9⟩) == (⟨7, 9⟩ : IntSize)
#guard rect.fromVector (rect.toVector ⟨1, 2, 3, 4⟩) == (⟨1, 2, 3, 4⟩ : Rect)
#guard color.fromVector (color.toVector .red) == Color.red
-- int converters round back to nearest
#guard intOffset.fromVector (.v2 2.6 (-1.4)) == (⟨3, -1⟩ : IntOffset)
-- color channels clamp on overshoot
#guard color.fromVector (.v4 1.2 (-0.1) 0.5 1.0) == ({ r := 1, g := 0, b := 0.5 } : Color)

end VectorConverter

end Compose
