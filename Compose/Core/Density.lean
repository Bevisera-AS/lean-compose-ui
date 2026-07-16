module

public section

namespace Compose

/-- A density-independent pixel dimension. Mirrors `androidx.compose.ui.unit.Dp`.

Numeric literals work directly: `(16 : Dp)`, `(2.5 : Dp)`; `Nat.dp`/`Float.dp`
give Compose-style postfix (`16 |>.dp`) where a literal isn't in `Dp` position. -/
structure Dp where
  value : Float32
  deriving Repr, BEq, Inhabited

namespace Dp

instance (n : Nat) : OfNat Dp n := ⟨⟨n.toFloat32⟩⟩
instance : OfScientific Dp := ⟨fun m e d => ⟨OfScientific.ofScientific m e d⟩⟩
instance : Add Dp := ⟨fun a b => ⟨a.value + b.value⟩⟩
instance : Sub Dp := ⟨fun a b => ⟨a.value - b.value⟩⟩
instance : Neg Dp := ⟨fun a => ⟨-a.value⟩⟩
instance : HMul Dp Float32 Dp := ⟨fun a s => ⟨a.value * s⟩⟩
instance : HDiv Dp Float32 Dp := ⟨fun a s => ⟨a.value / s⟩⟩
instance : LT Dp := ⟨fun a b => a.value < b.value⟩
instance : LE Dp := ⟨fun a b => a.value ≤ b.value⟩
instance : DecidableLT Dp := fun a b => inferInstanceAs (Decidable (a.value < b.value))
instance : DecidableLE Dp := fun a b => inferInstanceAs (Decidable (a.value ≤ b.value))
instance : Min Dp := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max Dp := ⟨fun a b => if a ≤ b then b else a⟩

/-- Sentinel for an unbounded dimension. -/
def infinity : Dp := ⟨3.402823e38⟩

def lerp (a b : Dp) (t : Float32) : Dp := ⟨a.value + (b.value - a.value) * t⟩

#guard (16 : Dp) + (8 : Dp) == (24 : Dp)
#guard (2.5 : Dp) == ⟨2.5⟩
#guard min (4 : Dp) (7 : Dp) == (4 : Dp)
#guard lerp (0 : Dp) (10 : Dp) 0.5 == (5 : Dp)

end Dp

def Nat.dp (n : Nat) : Dp := ⟨n.toFloat32⟩
def Float.dp (f : Float) : Dp := ⟨f.toFloat32⟩

/-- A scaled font-size unit. Mirrors `TextUnit` in sp. Literals: `(14 : Sp)`. -/
structure Sp where
  value : Float32
  deriving Repr, BEq, Inhabited

namespace Sp

instance (n : Nat) : OfNat Sp n := ⟨⟨n.toFloat32⟩⟩
instance : OfScientific Sp := ⟨fun m e d => ⟨OfScientific.ofScientific m e d⟩⟩
instance : HMul Sp Float32 Sp := ⟨fun a s => ⟨a.value * s⟩⟩

#guard (14 : Sp) == ⟨14.0⟩

end Sp

/-- Conversion context between `Dp`/`Sp` and pixels.
Mirrors `androidx.compose.ui.unit.Density`. `density` comes from the window's
display scale; `fontScale` is a user preference multiplier for text. -/
structure Density where
  density : Float32 := 1.0
  fontScale : Float32 := 1.0
  deriving Repr, BEq, Inhabited

namespace Density

def dpToPx (d : Density) (dp : Dp) : Float32 := dp.value * d.density

def dpRoundToPx (d : Density) (dp : Dp) : Int32 :=
  (d.dpToPx dp + 0.5).toInt32

def pxToDp (d : Density) (px : Float32) : Dp := ⟨px / d.density⟩

def spToPx (d : Density) (sp : Sp) : Float32 := sp.value * d.density * d.fontScale

#guard ({ density := 2.0 : Density }).dpToPx 16 == 32
#guard ({ density := 2.0 : Density }).dpRoundToPx ⟨7.8⟩ == 16
#guard ({ density := 2.0 : Density }).pxToDp 32 == (16 : Dp)
#guard ({ density := 2.0, fontScale := 1.5 : Density }).spToPx 10 == 30

end Density

end Compose

end
