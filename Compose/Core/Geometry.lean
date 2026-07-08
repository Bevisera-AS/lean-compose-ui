namespace Compose

/-- A 2D position or vector in pixels. Mirrors `androidx.compose.ui.geometry.Offset`. -/
structure Offset where
  x : Float32
  y : Float32
  deriving Repr, BEq, Inhabited

namespace Offset

def zero : Offset := ⟨0, 0⟩

instance : Add Offset := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub Offset := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩
instance : Neg Offset := ⟨fun a => ⟨-a.x, -a.y⟩⟩
instance : HMul Offset Float32 Offset := ⟨fun a s => ⟨a.x * s, a.y * s⟩⟩

def dot (a b : Offset) : Float32 := a.x * b.x + a.y * b.y

def distanceSquared (a b : Offset) : Float32 :=
  let d := a - b
  d.dot d

def distance (a b : Offset) : Float32 := (distanceSquared a b).sqrt

def lerp (a b : Offset) (t : Float32) : Offset := a + (b - a) * t

#guard (⟨1, 2⟩ + ⟨3, 4⟩ : Offset) == ⟨4, 6⟩
#guard (⟨3, 4⟩ - ⟨1, 2⟩ : Offset) == ⟨2, 2⟩
#guard ((⟨1, 2⟩ : Offset) * (2 : Float32)) == ⟨2, 4⟩
#guard distance ⟨0, 0⟩ ⟨3, 4⟩ == 5
#guard lerp ⟨0, 0⟩ ⟨10, 20⟩ 0.5 == ⟨5, 10⟩

end Offset

/-- A 2D extent in pixels. Mirrors `androidx.compose.ui.geometry.Size`. -/
structure Size where
  width : Float32
  height : Float32
  deriving Repr, BEq, Inhabited

namespace Size

def zero : Size := ⟨0, 0⟩

def isEmpty (s : Size) : Bool := s.width <= 0 || s.height <= 0

def center (s : Size) : Offset := ⟨s.width / 2, s.height / 2⟩

#guard (⟨0, 10⟩ : Size).isEmpty
#guard !(⟨1, 1⟩ : Size).isEmpty
#guard (⟨10, 20⟩ : Size).center == ⟨5, 10⟩

end Size

/-- An axis-aligned rectangle in pixels, `left/top` inclusive edges.
Mirrors `androidx.compose.ui.geometry.Rect`. -/
structure Rect where
  left : Float32
  top : Float32
  right : Float32
  bottom : Float32
  deriving Repr, BEq, Inhabited

namespace Rect

def zero : Rect := ⟨0, 0, 0, 0⟩

def ofOffsetSize (o : Offset) (s : Size) : Rect :=
  ⟨o.x, o.y, o.x + s.width, o.y + s.height⟩

def ofSize (s : Size) : Rect := ofOffsetSize .zero s

def width (r : Rect) : Float32 := r.right - r.left
def height (r : Rect) : Float32 := r.bottom - r.top
def size (r : Rect) : Size := ⟨r.width, r.height⟩
def topLeft (r : Rect) : Offset := ⟨r.left, r.top⟩
def center (r : Rect) : Offset := ⟨(r.left + r.right) / 2, (r.top + r.bottom) / 2⟩

def isEmpty (r : Rect) : Bool := r.right <= r.left || r.bottom <= r.top

def translate (r : Rect) (o : Offset) : Rect :=
  ⟨r.left + o.x, r.top + o.y, r.right + o.x, r.bottom + o.y⟩

/-- Grow (positive `d`) or shrink (negative `d`) on all sides. -/
def inflate (r : Rect) (d : Float32) : Rect :=
  ⟨r.left - d, r.top - d, r.right + d, r.bottom + d⟩

def contains (r : Rect) (p : Offset) : Bool :=
  r.left <= p.x && p.x < r.right && r.top <= p.y && p.y < r.bottom

def intersect (a b : Rect) : Rect :=
  ⟨max a.left b.left, max a.top b.top, min a.right b.right, min a.bottom b.bottom⟩

def overlaps (a b : Rect) : Bool :=
  a.left < b.right && b.left < a.right && a.top < b.bottom && b.top < a.bottom

def union (a b : Rect) : Rect :=
  ⟨min a.left b.left, min a.top b.top, max a.right b.right, max a.bottom b.bottom⟩

#guard ofOffsetSize ⟨1, 2⟩ ⟨10, 20⟩ == ⟨1, 2, 11, 22⟩
#guard (⟨0, 0, 10, 10⟩ : Rect).contains ⟨5, 5⟩
#guard !(⟨0, 0, 10, 10⟩ : Rect).contains ⟨10, 5⟩   -- right edge exclusive
#guard (⟨0, 0, 10, 10⟩ : Rect).contains ⟨0, 0⟩     -- left edge inclusive
#guard intersect ⟨0, 0, 10, 10⟩ ⟨5, 5, 20, 20⟩ == ⟨5, 5, 10, 10⟩
#guard (intersect ⟨0, 0, 4, 4⟩ ⟨5, 5, 9, 9⟩).isEmpty
#guard overlaps ⟨0, 0, 10, 10⟩ ⟨9, 9, 20, 20⟩
#guard !overlaps ⟨0, 0, 10, 10⟩ ⟨10, 0, 20, 10⟩
#guard union ⟨0, 0, 1, 1⟩ ⟨5, 5, 9, 9⟩ == ⟨0, 0, 9, 9⟩
#guard (⟨0, 0, 10, 10⟩ : Rect).translate ⟨2, 3⟩ == ⟨2, 3, 12, 13⟩
#guard (⟨2, 2, 8, 8⟩ : Rect).inflate 2 == ⟨0, 0, 10, 10⟩

end Rect

/-- Integer 2D position, used by layout placement. Mirrors `IntOffset`. -/
structure IntOffset where
  x : Int32
  y : Int32
  deriving Repr, BEq, Inhabited

namespace IntOffset

def zero : IntOffset := ⟨0, 0⟩

instance : Add IntOffset := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub IntOffset := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩

def toOffset (o : IntOffset) : Offset := ⟨o.x.toFloat32, o.y.toFloat32⟩

#guard (⟨1, 2⟩ + ⟨3, 4⟩ : IntOffset) == ⟨4, 6⟩

end IntOffset

/-- Integer 2D extent, used by layout measurement. Mirrors `IntSize`. -/
structure IntSize where
  width : Int32
  height : Int32
  deriving Repr, BEq, Inhabited

namespace IntSize

def zero : IntSize := ⟨0, 0⟩

def toSize (s : IntSize) : Size := ⟨s.width.toFloat32, s.height.toFloat32⟩

end IntSize

/-- Radii of one rounded-rect corner. Mirrors `CornerRadius`. -/
structure CornerRadius where
  x : Float32
  y : Float32
  deriving Repr, BEq, Inhabited

namespace CornerRadius

def zero : CornerRadius := ⟨0, 0⟩

def circular (r : Float32) : CornerRadius := ⟨r, r⟩

end CornerRadius

/-- A rectangle with per-corner radii. Mirrors `RoundRect`. -/
structure RoundRect where
  rect : Rect
  topLeft : CornerRadius := .zero
  topRight : CornerRadius := .zero
  bottomRight : CornerRadius := .zero
  bottomLeft : CornerRadius := .zero
  deriving Repr, BEq, Inhabited

namespace RoundRect

def ofRect (r : Rect) : RoundRect := { rect := r }

def circular (r : Rect) (radius : Float32) : RoundRect :=
  let c := CornerRadius.circular radius
  { rect := r, topLeft := c, topRight := c, bottomRight := c, bottomLeft := c }

/-- Clamp all radii so adjacent corners never overlap (each axis pair sums to at
most the side length), preserving proportions — the standard CSS/Skia rule. -/
def normalize (rr : RoundRect) : RoundRect :=
  let w := rr.rect.width
  let h := rr.rect.height
  let ratio (side a b : Float32) : Float32 :=
    if a + b > side && a + b > 0 then side / (a + b) else 1
  let s := min (min (ratio w rr.topLeft.x rr.topRight.x)
                    (ratio w rr.bottomLeft.x rr.bottomRight.x))
               (min (ratio h rr.topLeft.y rr.bottomLeft.y)
                    (ratio h rr.topRight.y rr.bottomRight.y))
  if s >= 1 then rr
  else
    let f (c : CornerRadius) : CornerRadius := ⟨c.x * s, c.y * s⟩
    { rr with
      topLeft := f rr.topLeft, topRight := f rr.topRight
      bottomRight := f rr.bottomRight, bottomLeft := f rr.bottomLeft }

#guard (circular ⟨0, 0, 10, 10⟩ 2).normalize == circular ⟨0, 0, 10, 10⟩ 2
#guard (circular ⟨0, 0, 10, 10⟩ 10).normalize == circular ⟨0, 0, 10, 10⟩ 5

end RoundRect

end Compose
