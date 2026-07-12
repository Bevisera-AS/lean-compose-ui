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

/-- Distance from `p` to the closed segment `a`–`b` (clamped projection; a
degenerate segment is its point). -/
def distToSegment (p a b : Offset) : Float32 :=
  let d := b - a
  let len2 := d.dot d
  if len2 <= 1e-9 then distance p a
  else
    let t := min 1 (max 0 (dot (p - a) d / len2))
    distance p (a + d * t)

#guard distToSegment ⟨5, 3⟩ ⟨0, 0⟩ ⟨10, 0⟩ == 3       -- above the middle
#guard distToSegment ⟨-3, 4⟩ ⟨0, 0⟩ ⟨10, 0⟩ == 5      -- beyond an endpoint
#guard distToSegment ⟨7, 7⟩ ⟨2, 2⟩ ⟨2, 2⟩ == distance ⟨7, 7⟩ ⟨2, 2⟩

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

/-- A 2D affine transform, column-vector convention (Skia/Compose):
`p' = (a·x + c·y + tx, b·x + d·y + ty)`. Identity by default. -/
structure Affine where
  /-- X scale (`m00`). -/
  a : Float32 := 1
  /-- Y skew (`m10`). -/
  b : Float32 := 0
  /-- X skew (`m01`). -/
  c : Float32 := 0
  /-- Y scale (`m11`). -/
  d : Float32 := 1
  /-- X translation. -/
  tx : Float32 := 0
  /-- Y translation. -/
  ty : Float32 := 0
  deriving Repr, BEq, Inhabited

namespace Affine

def identity : Affine := {}

def translation (o : Offset) : Affine := { tx := o.x, ty := o.y }

def scaling (sx sy : Float32) : Affine := { a := sx, d := sy }

/-- Rotation by `rad` radians (clockwise in the y-down screen frame). -/
def rotation (rad : Float32) : Affine :=
  let cs := (Float.cos rad.toFloat).toFloat32
  let sn := (Float.sin rad.toFloat).toFloat32
  { a := cs, b := sn, c := -sn, d := cs }

/-- Composition: `(f.comp g).mapOffset p = f.mapOffset (g.mapOffset p)`
(apply `g` first). -/
def comp (f g : Affine) : Affine :=
  { a := f.a * g.a + f.c * g.b
    b := f.b * g.a + f.d * g.b
    c := f.a * g.c + f.c * g.d
    d := f.b * g.c + f.d * g.d
    tx := f.a * g.tx + f.c * g.ty + f.tx
    ty := f.b * g.tx + f.d * g.ty + f.ty }

def mapOffset (m : Affine) (p : Offset) : Offset :=
  ⟨m.a * p.x + m.c * p.y + m.tx, m.b * p.x + m.d * p.y + m.ty⟩

def det (m : Affine) : Float32 := m.a * m.d - m.b * m.c

/-- The inverse transform, or `none` when degenerate (`|det| ≤ 1e-9`). -/
def invert? (m : Affine) : Option Affine :=
  let dt := m.det
  if dt.abs <= 1e-9 then none
  else
    let ia := m.d / dt
    let ib := -m.b / dt
    let ic := -m.c / dt
    let idd := m.a / dt
    some { a := ia, b := ib, c := ic, d := idd
           tx := -(ia * m.tx + ic * m.ty), ty := -(ib * m.tx + idd * m.ty) }

/-- The axis-aligned bounding box of the mapped rectangle's four corners. -/
def mapRect (m : Affine) (r : Rect) : Rect :=
  let p0 := m.mapOffset ⟨r.left, r.top⟩
  let p1 := m.mapOffset ⟨r.right, r.top⟩
  let p2 := m.mapOffset ⟨r.left, r.bottom⟩
  let p3 := m.mapOffset ⟨r.right, r.bottom⟩
  ⟨min (min p0.x p1.x) (min p2.x p3.x), min (min p0.y p1.y) (min p2.y p3.y),
   max (max p0.x p1.x) (max p2.x p3.x), max (max p0.y p1.y) (max p2.y p3.y)⟩

def isTranslationOnly (m : Affine) : Bool :=
  m.a == 1 && m.b == 0 && m.c == 0 && m.d == 1

def isIdentity (m : Affine) : Bool :=
  m.isTranslationOnly && m.tx == 0 && m.ty == 0

/-- Component-wise approximate equality (trig-built transforms carry rounding). -/
def approxEq (m n : Affine) (eps : Float32 := 1e-5) : Bool :=
  (m.a - n.a).abs <= eps && (m.b - n.b).abs <= eps && (m.c - n.c).abs <= eps
    && (m.d - n.d).abs <= eps && (m.tx - n.tx).abs <= eps && (m.ty - n.ty).abs <= eps

/-- Whether a layer composited through `m` should snap to the pixel grid and
sample nearest: pure translations within `eps` of a whole pixel (the crisp,
parity-stable case — static content and settled animations); everything else
places fractionally with linear filtering. The subpixel-text heuristic —
identity-ish composites keep text byte-identical to unlayered rendering. -/
def snapComposite (m : Affine) (eps : Float32 := 1 / 64) : Bool :=
  m.isTranslationOnly
    && (m.tx - m.tx.round).abs <= eps && (m.ty - m.ty.round).abs <= eps

private def pi32 : Float32 := (3.14159265358979323846 : Float).toFloat32

-- identity / composition / inverse
#guard Affine.identity.mapOffset ⟨3, 4⟩ == ⟨3, 4⟩
#guard (translation ⟨2, 3⟩).mapOffset ⟨1, 1⟩ == ⟨3, 4⟩
#guard (scaling 2 3).mapOffset ⟨4, 5⟩ == ⟨8, 15⟩
#guard ((translation ⟨2, 3⟩).comp (scaling 2 2)).mapOffset ⟨1, 1⟩ == ⟨4, 5⟩
#guard ((scaling 2 2).comp (translation ⟨2, 3⟩)).mapOffset ⟨1, 1⟩ == ⟨6, 8⟩
#guard ((translation ⟨5, -2⟩).comp (translation ⟨-5, 2⟩)).isIdentity
#guard (rotation (pi32 / 2)).approxEq { a := 0, b := 1, c := -1, d := 0 }
#guard ((rotation 0.7).comp (rotation (-0.7))).approxEq .identity
#guard (((rotation 0.5).comp (scaling 2 3)).invert?.getD .identity).comp
        ((rotation 0.5).comp (scaling 2 3)) |>.approxEq .identity
#guard (scaling 1 0).invert? == none
#guard (scaling 2 3).det == 6
-- mapRect: 90° about the origin maps (1,2,3,4) to x=-4..-2, y=1..3
#guard (((rotation (pi32 / 2)).mapRect ⟨1, 2, 3, 4⟩).left + 4).abs <= 1e-5
#guard (((rotation (pi32 / 2)).mapRect ⟨1, 2, 3, 4⟩).top - 1).abs <= 1e-5
#guard (translation ⟨10, 20⟩).mapRect ⟨0, 0, 4, 4⟩ == ⟨10, 20, 14, 24⟩
-- classification + snap heuristic
#guard (translation ⟨5, 6⟩).isTranslationOnly && !(translation ⟨5, 6⟩).isIdentity
#guard !(scaling 2 1).isTranslationOnly
#guard (translation ⟨5, 6⟩).snapComposite
#guard (translation ⟨5.004, 6⟩).snapComposite          -- within 1/64 of the grid
#guard !(translation ⟨5.4, 6⟩).snapComposite
#guard !(rotation 0.3).snapComposite
#guard !((scaling 1.5 1.5).comp (translation ⟨1, 1⟩)).snapComposite

end Affine

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

/-- Translate the rounded rect by `o` (radii unchanged). Mirrors
`RoundRect.translate`. -/
def translate (rr : RoundRect) (o : Offset) : RoundRect :=
  { rr with rect := rr.rect.translate o }

#guard (circular ⟨0, 0, 10, 10⟩ 2).translate ⟨5, 6⟩ == circular ⟨5, 6, 15, 16⟩ 2

/-- Whether `p` lies inside the rounded rect: inside the bounding rect and, in
each corner's radius box, inside that corner's ellipse. The exact geometric
containment test pointer hit-testing uses for `Modifier.clip`ped nodes.
Mirrors the corner math of Skia's `SkRRect::contains`. -/
def contains (rr : RoundRect) (p : Offset) : Bool :=
  rr.rect.contains p &&
  cornerOk rr.topLeft (rr.rect.left + rr.topLeft.x) (rr.rect.top + rr.topLeft.y)
    (p.x < rr.rect.left + rr.topLeft.x) (p.y < rr.rect.top + rr.topLeft.y) p &&
  cornerOk rr.topRight (rr.rect.right - rr.topRight.x) (rr.rect.top + rr.topRight.y)
    (p.x > rr.rect.right - rr.topRight.x) (p.y < rr.rect.top + rr.topRight.y) p &&
  cornerOk rr.bottomRight (rr.rect.right - rr.bottomRight.x) (rr.rect.bottom - rr.bottomRight.y)
    (p.x > rr.rect.right - rr.bottomRight.x) (p.y > rr.rect.bottom - rr.bottomRight.y) p &&
  cornerOk rr.bottomLeft (rr.rect.left + rr.bottomLeft.x) (rr.rect.bottom - rr.bottomLeft.y)
    (p.x < rr.rect.left + rr.bottomLeft.x) (p.y > rr.rect.bottom - rr.bottomLeft.y) p
where
  /-- Inside the corner's radius box (`inX && inY`), test the ellipse centered
  at `(cx, cy)`; outside the box the corner imposes nothing. -/
  cornerOk (c : CornerRadius) (cx cy : Float32) (inX inY : Bool) (p : Offset) : Bool :=
    !(inX && inY && c.x > 0 && c.y > 0) ||
    (let dx := (p.x - cx) / c.x
     let dy := (p.y - cy) / c.y
     dx * dx + dy * dy <= 1)

-- plain rect: corners impose nothing
#guard (ofRect ⟨0, 0, 10, 10⟩).contains ⟨0, 0⟩
#guard !(ofRect ⟨0, 0, 10, 10⟩).contains ⟨10, 5⟩
-- circle of radius 20 at (20,20): corners of the bounding box are outside
#guard (circular ⟨0, 0, 40, 40⟩ 20).contains ⟨20, 20⟩
#guard !(circular ⟨0, 0, 40, 40⟩ 20).contains ⟨2, 2⟩
#guard !(circular ⟨0, 0, 40, 40⟩ 20).contains ⟨38, 38⟩
#guard (circular ⟨0, 0, 40, 40⟩ 20).contains ⟨20, 1⟩   -- on the vertical axis
#guard (circular ⟨0, 0, 40, 40⟩ 20).contains ⟨6, 6⟩    -- (14² + 14²) ≤ 20²
-- rounded rect: straight edges hit, radius-box corners follow the arc
#guard (circular ⟨0, 0, 40, 20⟩ 5).contains ⟨1, 10⟩
#guard !(circular ⟨0, 0, 40, 20⟩ 5).contains ⟨1, 1⟩
#guard (circular ⟨0, 0, 40, 20⟩ 5).contains ⟨4, 4⟩
-- translated rect
#guard (circular ⟨10, 10, 50, 50⟩ 20).contains ⟨30, 30⟩
#guard !(circular ⟨10, 10, 50, 50⟩ 20).contains ⟨12, 12⟩

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
