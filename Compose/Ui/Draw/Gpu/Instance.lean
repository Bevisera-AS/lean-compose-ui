import Compose.Core.Color
import Compose.Core.Geometry
import Sdl.Ttf

/-!
# GPU instance & vertex layouts (`Compose/Ui/Draw/Gpu/Instance.lean`)

Pure byte packers for the GPU pipelines' per-instance and per-vertex data
(little-endian, exactly the strides the pipelines in `Gpu/Shaders.lean`
declare — pinned by the `#guard`s below), plus the flat draw-command list the
encoder emits and the renderer replays, and the resolved-text input the
encoder consumes (fetched from SDL_ttf's GPU text engine by
`Gpu/TextEngine.lean`).

Colors travel non-premultiplied (gradient/vertex interpolation then matches
the CPU `Color.lerp` and the SDL backend's vertex colors exactly); the
fragment shaders premultiply after coverage.
-/

namespace Compose.Draw.Gpu

/-! ## Byte packing -/

/-- Append a `Float32` little-endian (IEEE-754 bits). -/
def pushF32 (b : ByteArray) (f : Float32) : ByteArray :=
  let v := f.toBits
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8
    |>.push (v >>> 24).toUInt8

/-- Append a `UInt32` little-endian. -/
def pushU32 (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8
    |>.push (v >>> 24).toUInt8

/-- Append a non-premultiplied color as four `Float32`s. -/
def pushColor (b : ByteArray) (c : Color) : ByteArray :=
  pushF32 (pushF32 (pushF32 (pushF32 b c.r) c.g) c.b) c.a

/-! ## Quad instances (the SDF pipeline) -/

/-- One instance of the quad pipeline: an axis-aligned (rounded) rectangle
with either a fill brush (solid or two-stop linear gradient) or a centered
stroke, masked by a (rounded) clip rect. 144 bytes = 9 `float4` attributes. -/
structure QuadInstance where
  /-- Shape origin and size in target px. -/
  origin : Offset := .zero
  size : Size := .zero
  /-- Per-corner circular radii `(tl, tr, br, bl)`. -/
  radiusTL : Float32 := 0
  radiusTR : Float32 := 0
  radiusBR : Float32 := 0
  radiusBL : Float32 := 0
  /-- Fill colors: gradient endpoints (equal for a solid fill). -/
  bg0 : Color := ⟨0, 0, 0, 0⟩
  bg1 : Color := ⟨0, 0, 0, 0⟩
  /-- Gradient projection: `t = saturate(dot(p - gradStart, gradDir))`, with
  `gradDir` premultiplied by `1/len²`. Zero for solid fills (`t = 0`). -/
  gradStart : Offset := .zero
  gradDir : Offset := .zero
  /-- Centered-stroke paint; `borderWidth = 0` means fill. -/
  borderColor : Color := ⟨0, 0, 0, 0⟩
  borderWidth : Float32 := 0
  /-- Rounded clip mask in target px (a huge rect when unclipped). -/
  clipOrigin : Offset := ⟨-1e8, -1e8⟩
  clipSize : Size := ⟨2e8, 2e8⟩
  clipRadiusTL : Float32 := 0
  clipRadiusTR : Float32 := 0
  clipRadiusBR : Float32 := 0
  clipRadiusBL : Float32 := 0
  deriving Repr, BEq, Inhabited

/-- Bytes-per-instance of the quad pipeline. -/
def quadStride : Nat := 144

/-- Pack one `QuadInstance` (144 bytes; attribute order matches the
`quad_vertex` MSL `[[attribute(n)]]` declarations). -/
def QuadInstance.pack (q : QuadInstance) (b : ByteArray) : ByteArray := Id.run do
  let mut b := b
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.origin.x) q.origin.y) q.size.width) q.size.height
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.radiusTL) q.radiusTR) q.radiusBR) q.radiusBL
  b := pushColor b q.bg0
  b := pushColor b q.bg1
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.gradStart.x) q.gradStart.y) q.gradDir.x) q.gradDir.y
  b := pushColor b q.borderColor
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.borderWidth) 0) 0) 0
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.clipOrigin.x) q.clipOrigin.y) q.clipSize.width) q.clipSize.height
  b := pushF32 (pushF32 (pushF32 (pushF32 b q.clipRadiusTL) q.clipRadiusTR) q.clipRadiusBR) q.clipRadiusBL
  return b

#guard (({} : QuadInstance).pack .empty).size == quadStride

/-! ## Shadow instances (the analytic Gaussian pipeline) -/

/-- One instance of the shadow pipeline: a Gaussian-blurred rounded rect
(Evan Wallace's analytic form — the fragment shader is the MSL twin of
`Gpu.Sdf.shadow`). The drop-shadow offset is already applied to `origin`;
the vertex shader inflates the quad by `3σ + 1` px on every side.
48 bytes = 3 `float4` attributes. -/
structure ShadowInstance where
  /-- Shadow-casting rect (offset applied) in target px. -/
  origin : Offset := .zero
  size : Size := .zero
  /-- Shadow color (non-premultiplied; the fragment premultiplies after the
  blurred coverage). -/
  color : Color := ⟨0, 0, 0, 0⟩
  /-- Gaussian standard deviation (`blur / 2`). -/
  sigma : Float32 := 1
  /-- Circular corner radius (per-corner radii degrade to the top-left one —
  the analytic form integrates a single corner). -/
  corner : Float32 := 0
  deriving Repr, BEq, Inhabited

/-- Bytes-per-instance of the shadow pipeline. -/
def shadowStride : Nat := 48

/-- Pack one `ShadowInstance` (48 bytes; attribute order matches the
`shadow_vertex` MSL `[[attribute(n)]]` declarations). -/
def ShadowInstance.pack (s : ShadowInstance) (b : ByteArray) : ByteArray :=
  let b := pushF32 (pushF32 (pushF32 (pushF32 b s.origin.x) s.origin.y) s.size.width) s.size.height
  let b := pushColor b s.color
  pushF32 (pushF32 (pushF32 (pushF32 b s.sigma) s.corner) 0) 0

#guard (({} : ShadowInstance).pack .empty).size == shadowStride

/-! ## Mesh and glyph vertices -/

/-- Bytes-per-vertex of the mesh pipeline: `pos float2 + color float4`. -/
def meshVertexStride : Nat := 24

/-- Pack one mesh vertex (24 bytes): position + non-premultiplied color —
the exact data `Renderer.geometry` receives on the SDL backend, so the
tessellator-fallback path (arcs, angled lines, the clipped ripple,
multi-stop gradients) interpolates identically. -/
def packMeshVertex (b : ByteArray) (pos : Offset) (color : Color) : ByteArray :=
  pushColor (pushF32 (pushF32 b pos.x) pos.y) color

#guard (packMeshVertex .empty ⟨1, 2⟩ .red).size == meshVertexStride

/-- Bytes-per-vertex of the glyph pipeline: `pos float2 + uv float2 +
color float4`. -/
def texVertexStride : Nat := 32

/-- Pack one glyph vertex (32 bytes): snapped position, atlas UV, run color. -/
def packTexVertex (b : ByteArray) (pos uv : Offset) (color : Color) : ByteArray :=
  pushColor (pushF32 (pushF32 (pushF32 (pushF32 b pos.x) pos.y) uv.x) uv.y) color

#guard (packTexVertex .empty ⟨1, 2⟩ ⟨0, 1⟩ .red).size == texVertexStride

/-! ## Draw commands -/

/-- One replayable draw, referencing ranges of the frame's packed buffers.
`scissor` is the integer clip in target px (`none` = full target), computed
with the same floor/ceil pixel expansion as the SDL backend's clip — the two
backends clip identically. -/
inductive DrawCmd where
  /-- `count` quad instances starting at instance `first`
  (`drawPrimitives 4 count 0 first`). -/
  | quads (first count : Nat) (scissor : Option Sdl.Rect)
  /-- `count` mesh indices starting at index `first` (indices are absolute
  into the frame's mesh vertex buffer; `vertexOffset` stays 0 so consecutive
  meshes merge). -/
  | mesh (first count : Nat) (scissor : Option Sdl.Rect)
  /-- `count` glyph indices starting at index `first`, sampling the frame's
  atlas texture `atlas` (an index into the resolved atlas table). -/
  | glyphs (first count : Nat) (atlas : Nat) (scissor : Option Sdl.Rect)
  /-- `count` shadow instances starting at instance `first`. -/
  | shadows (first count : Nat) (scissor : Option Sdl.Rect)
  /-- Composite offscreen layer `idx` (an index into the frame's layer table)
  as one premultiplied textured quad at the layer's bounds. -/
  | layer (idx : Nat) (scissor : Option Sdl.Rect)
  /-- `count` image indices starting at index `first`, sampling the frame's
  image texture `tex` (an index into the resolved image table) with the
  linear or nearest sampler. Rides the layer pipeline — image textures hold
  premultiplied pixels. -/
  | image (first count : Nat) (tex : Nat) (linear : Bool) (scissor : Option Sdl.Rect)
  deriving Repr, BEq, Inhabited

/-! ## Resolved text input

`Text.gpuDrawData` is IO (it walks SDL_ttf's live atlas state), so the
renderer resolves every text run *before* the pure encode
(`Gpu/TextEngine.lean`) and hands the encoder this plain data. -/

/-- One atlas draw sequence of a text run, with the atlas texture replaced by
an index into the frame's atlas table. `xy` is SDL_ttf's y-up layout relative
to the run's top-left origin (probe-verified: `screen = origin + (x, -y)`). -/
structure ResolvedSeq where
  /-- Index into the frame's atlas texture table. -/
  atlas : Nat
  /-- Vertex positions, `2 × n` floats, y-up relative to the run origin. -/
  xy : FloatArray
  /-- Normalized atlas UVs, `2 × n` floats. -/
  uv : FloatArray
  /-- Triangle indices into the sequence's vertices. -/
  indices : Array Int32
  /-- Glyph image type (`.alpha` tinted by the run color; `.color` emoji drawn
  with a white vertex color). -/
  imageType : Sdl.Ttf.ImageType

/-- All sequences of one recorded text run, in `Prim`-walk order. -/
abbrev ResolvedRun := Array ResolvedSeq

end Compose.Draw.Gpu
