import Compose.Core.Color
import Compose.Core.Geometry

/-!
# Draw meshes (`Compose/Ui/Draw/Mesh.lean`)

A pure, SDL-free triangle-mesh representation shared by the tessellator
(`Compose/Ui/Draw/Tessellate.lean`) and the SDL backend
(`Compose/Ui/Draw/Scope.lean`). Conversion to `Sdl.Vertex` happens only in the
backend; nothing here touches SDL or `IO`.

There is no direct Compose analog — Compose tessellates inside Skia — but a
`Mesh` plays the role of Skia's `SkVertices` (positions + per-vertex colors +
an index buffer) for our software-tessellated anti-aliasing.
-/

namespace Compose.Draw

/-- One tessellated vertex: a position in pixels and a non-premultiplied color
(alpha `0` marks a feather-ring vertex). Analogous to a single entry of Skia's
`SkVertices` position/color arrays. -/
structure DVertex where
  /-- Vertex position in pixels. -/
  pos : Offset
  /-- Vertex color (sRGB, non-premultiplied); alpha `0` = fully feathered edge. -/
  color : Color
  deriving Repr, BEq, Inhabited

/-- A triangle mesh: a vertex buffer plus a flat triangle-index buffer (every
three entries name one triangle). Indices are stored as `Int32` — the exact
representation `Renderer.geometry` consumes — so cached meshes reach SDL with
no per-emit index conversion; they are always non-negative and point inside
`vertices`. Analogous to Skia's `SkVertices`. -/
structure Mesh where
  /-- Vertex buffer. -/
  vertices : Array DVertex := #[]
  /-- Flat triangle index buffer (`indices.size` is a multiple of three),
  `Int32`-encoded for `Renderer.geometry`. -/
  indices : Array Int32 := #[]
  deriving Repr, BEq, Inhabited

namespace Mesh

/-- The empty mesh (no vertices, no triangles). -/
def empty : Mesh := {}

/-- Whether the mesh has no triangles. -/
def isEmpty (m : Mesh) : Bool := m.indices.isEmpty

/-- Number of vertices. -/
def vertexCount (m : Mesh) : Nat := m.vertices.size

/-- Number of triangles (`indices.size / 3`). -/
def triangleCount (m : Mesh) : Nat := m.indices.size / 3

/-- Whether every index is non-negative and refers to an existing vertex — the
mesh well-formedness invariant the backend relies on. -/
def indicesInRange (m : Mesh) : Bool :=
  m.indices.all fun i => 0 ≤ i.toInt && i.toInt < (m.vertices.size : Int)

/-- Append `b` after `a`, renumbering `b`'s indices by `a`'s vertex count so the
combined index buffer stays valid. Builds output arrays linearly (FBIP). -/
def append (a b : Mesh) : Mesh := Id.run do
  if b.vertices.isEmpty then return a
  let base := Int32.ofNat a.vertices.size
  let mut vs := a.vertices
  for v in b.vertices do
    vs := vs.push v
  let mut is := a.indices
  for i in b.indices do
    is := is.push (i + base)
  return { vertices := vs, indices := is }

/-- Translate every vertex position by `o`, leaving colors untouched. -/
def translate (m : Mesh) (o : Offset) : Mesh :=
  { m with vertices := m.vertices.map fun v => { v with pos := v.pos + o } }

/-- Multiply every vertex alpha by `a` (used by the backend to fold an ambient
alpha multiplier into vertex colors). -/
def scaleAlpha (m : Mesh) (a : Float32) : Mesh :=
  { m with vertices := m.vertices.map fun v => { v with color := v.color.withAlpha (v.color.a * a) } }

/-- Bounding rect of the mesh's vertices (`none` when there are no vertices).
Feather-ring vertices are included, so this bounds everything the mesh can
touch. -/
def bounds (m : Mesh) : Option Rect := Id.run do
  let some v0 := m.vertices[0]? | return none
  let mut r : Rect := ⟨v0.pos.x, v0.pos.y, v0.pos.x, v0.pos.y⟩
  for v in m.vertices do
    r := ⟨min r.left v.pos.x, min r.top v.pos.y, max r.right v.pos.x, max r.bottom v.pos.y⟩
  return some r

#guard empty.isEmpty
#guard empty.vertexCount == 0
#guard empty.triangleCount == 0
#guard empty.indicesInRange

-- A single triangle appended to another shifts indices by the first's vertex count.
private def tri (o : Offset) (c : Color) : Mesh :=
  { vertices := #[⟨o, c⟩, ⟨o + ⟨1, 0⟩, c⟩, ⟨o + ⟨0, 1⟩, c⟩], indices := #[0, 1, 2] }

#guard (tri ⟨0, 0⟩ .red).triangleCount == 1
#guard (tri ⟨0, 0⟩ .red).indicesInRange
#guard (append (tri ⟨0, 0⟩ .red) (tri ⟨5, 5⟩ .blue)).vertexCount == 6
#guard (append (tri ⟨0, 0⟩ .red) (tri ⟨5, 5⟩ .blue)).indices == #[0, 1, 2, 3, 4, 5]
#guard (append (tri ⟨0, 0⟩ .red) (tri ⟨5, 5⟩ .blue)).indicesInRange
#guard (append empty (tri ⟨0, 0⟩ .red)) == tri ⟨0, 0⟩ .red
#guard (append (tri ⟨0, 0⟩ .red) empty) == tri ⟨0, 0⟩ .red
#guard ((tri ⟨0, 0⟩ .red).translate ⟨2, 3⟩).vertices[0]!.pos == ⟨2, 3⟩
#guard ((tri ⟨0, 0⟩ (Color.white.withAlpha 1.0)).scaleAlpha 0.5).vertices[0]!.color.a == 0.5
#guard (empty : Mesh).bounds == none
#guard (tri ⟨2, 3⟩ .red).bounds == some ⟨2, 3, 3, 4⟩
#guard (append (tri ⟨0, 0⟩ .red) (tri ⟨5, 5⟩ .blue)).bounds == some ⟨0, 0, 6, 6⟩

end Mesh

end Compose.Draw
