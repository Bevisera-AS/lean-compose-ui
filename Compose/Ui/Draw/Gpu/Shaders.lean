import Compose.Ui.Draw.Gpu.Instance
import Sdl

/-!
# GPU shaders & pipelines (`Compose/Ui/Draw/Gpu/Shaders.lean`)

The MSL shader sources (runtime-compiled — probe-verified the Metal backend
accepts MSL source) and the three M-b graphics pipelines:

- **quad**: instanced unit triangle strips (corners from `vertex_id`, all
  attributes instance-rate at `quadStride`), SDF fill/stroke coverage plus a
  rounded clip mask. The SDF/coverage formulas are twins of the `#guard`-tested
  Lean functions in `Gpu/Sdf.lean` (cited by name below).
- **mesh**: indexed triangles from the CPU tessellator (SDL-parity fallback).
- **glyph**: indexed textured triangles over SDL_ttf's GPU glyph atlas.

All pipelines blend premultiplied (`one / oneMinusSrcAlpha`); colors travel
non-premultiplied in vertex data and fragments premultiply after coverage, so
interpolation matches the SDL backend's non-premultiplied vertex colors.
Uniforms: one 16-byte `Globals { float2 viewport }` at vertex `[[buffer(0)]]`
(pushed once per command buffer); the shadow and layer pipelines land in M-c.
-/

namespace Compose.Draw.Gpu
open Sdl.Gpu

/-- Shared MSL prelude: the `Globals` uniform, NDC mapping, and the rounded-
rect SDF (twin of `Gpu.Sdf.rrectSdf`/`pickRadius`; bounds as `(x, y, w, h)`,
radii as `(tl, tr, br, bl)`). -/
private def mslPrelude : String := "
#include <metal_stdlib>
using namespace metal;

struct Globals { float2 viewport; };

static inline float4 to_ndc(float2 p, float2 viewport) {
  return float4(p / viewport * float2(2.0, -2.0) + float2(-1.0, 1.0), 0.0, 1.0);
}

static inline float pick_radius(float2 p, float2 center, float4 r) {
  return p.x < center.x ? (p.y < center.y ? r.x : r.w)
                        : (p.y < center.y ? r.y : r.z);
}

static inline float rrect_sdf(float2 p, float4 bounds, float4 radii) {
  float2 hs = bounds.zw * 0.5;
  float2 center = bounds.xy + hs;
  float r = pick_radius(p, center, radii);
  float2 d = abs(p - center) - hs + r;
  return length(max(d, 0.0)) + min(max(d.x, d.y), 0.0) - r;
}
"

/-- The quad pipeline's MSL: instance-rate attributes, unit-quad corners from
`vertex_id` (inflated by the stroke half-width plus a 1 px AA margin), and an
SDF fragment — centered-stroke band when `borderWidth > 0`, gradient/solid
fill coverage otherwise (`coverage(sdf) = saturate(0.5 - sdf)`, twin of
`Gpu.Sdf.coverage`), both masked by the rounded clip. -/
private def quadMsl : String := mslPrelude ++ "
struct QuadIn {
  float4 bounds     [[attribute(0)]];
  float4 radii      [[attribute(1)]];
  float4 bg0        [[attribute(2)]];
  float4 bg1        [[attribute(3)]];
  float4 gradient   [[attribute(4)]];
  float4 border     [[attribute(5)]];
  float4 borderW    [[attribute(6)]];
  float4 clipBounds [[attribute(7)]];
  float4 clipRadii  [[attribute(8)]];
};

struct QuadOut {
  float4 pos [[position]];
  float2 world;
  float4 bounds     [[flat]];
  float4 radii      [[flat]];
  float4 bg0        [[flat]];
  float4 bg1        [[flat]];
  float4 gradient   [[flat]];
  float4 border     [[flat]];
  float  borderW    [[flat]];
  float4 clipBounds [[flat]];
  float4 clipRadii  [[flat]];
};

vertex QuadOut quad_vertex(QuadIn in [[stage_in]], uint vid [[vertex_id]],
                           constant Globals& g [[buffer(0)]]) {
  float inflate = in.borderW.x * 0.5 + 1.0;
  float2 corner = float2(float(vid & 1u), float(vid >> 1u));
  float2 p = in.bounds.xy - inflate + corner * (in.bounds.zw + 2.0 * inflate);
  QuadOut out;
  out.pos = to_ndc(p, g.viewport);
  out.world = p;
  out.bounds = in.bounds;
  out.radii = in.radii;
  out.bg0 = in.bg0;
  out.bg1 = in.bg1;
  out.gradient = in.gradient;
  out.border = in.border;
  out.borderW = in.borderW.x;
  out.clipBounds = in.clipBounds;
  out.clipRadii = in.clipRadii;
  return out;
}

fragment float4 quad_fragment(QuadOut in [[stage_in]]) {
  float sdf = rrect_sdf(in.world, in.bounds, in.radii);
  float clip = saturate(0.5 - rrect_sdf(in.world, in.clipBounds, in.clipRadii));
  float4 src;
  float cov;
  if (in.borderW > 0.0) {
    src = in.border;
    cov = saturate(0.5 - (abs(sdf) - in.borderW * 0.5));
  } else {
    float t = saturate(dot(in.world - in.gradient.xy, in.gradient.zw));
    src = mix(in.bg0, in.bg1, t);
    cov = saturate(0.5 - sdf);
  }
  cov *= clip;
  return float4(src.rgb * src.a * cov, src.a * cov);
}
"

/-- The mesh pipeline's MSL: positions in target px, interpolated
non-premultiplied colors, premultiplied on output — the CPU tessellator's
feathered AA rasterizes exactly as on the SDL backend. -/
private def meshMsl : String := mslPrelude ++ "
struct MeshIn {
  float2 pos   [[attribute(0)]];
  float4 color [[attribute(1)]];
};

struct MeshOut {
  float4 pos [[position]];
  float4 color;
};

vertex MeshOut mesh_vertex(MeshIn in [[stage_in]],
                           constant Globals& g [[buffer(0)]]) {
  MeshOut out;
  out.pos = to_ndc(in.pos, g.viewport);
  out.color = in.color;
  return out;
}

fragment float4 mesh_fragment(MeshOut in [[stage_in]]) {
  return float4(in.color.rgb * in.color.a, in.color.a);
}
"

/-- The glyph pipeline's MSL: atlas texel × run color (alpha atlases carry
white RGB, so this tints; color-emoji runs pass a white vertex color),
premultiplied on output. -/
private def glyphMsl : String := mslPrelude ++ "
struct TexIn {
  float2 pos   [[attribute(0)]];
  float2 uv    [[attribute(1)]];
  float4 color [[attribute(2)]];
};

struct TexOut {
  float4 pos [[position]];
  float2 uv;
  float4 color;
};

vertex TexOut tex_vertex(TexIn in [[stage_in]],
                         constant Globals& g [[buffer(0)]]) {
  TexOut out;
  out.pos = to_ndc(in.pos, g.viewport);
  out.uv = in.uv;
  out.color = in.color;
  return out;
}

fragment float4 tex_fragment(TexOut in [[stage_in]],
                             texture2d<float> atlas [[texture(0)]],
                             sampler smp [[sampler(0)]]) {
  float4 t = atlas.sample(smp, in.uv);
  float4 c = t * in.color;
  return float4(c.rgb * c.a, c.a);
}
"

/-- The 16-byte `Globals` uniform (viewport size + pad). -/
def packGlobals (w h : Float32) : ByteArray := Id.run do
  let push (b : ByteArray) (f : Float32) : ByteArray :=
    let v := f.toBits
    b.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8
      |>.push (v >>> 24).toUInt8
  return push (push (push (push (ByteArray.emptyWithCapacity 16) w) h) 0) 0

#guard (packGlobals 800 600).size == 16

/-- Premultiplied-alpha blending — the one blend state every pipeline uses. -/
private def premulBlend : ColorTargetBlendState :=
  { srcColorBlendfactor := .one, dstColorBlendfactor := .oneMinusSrcAlpha
    colorBlendOp := .add
    srcAlphaBlendfactor := .one, dstAlphaBlendfactor := .oneMinusSrcAlpha
    alphaBlendOp := .add
    enableBlend := true }

/-- The M-b pipeline set for one color-target format. -/
structure Pipelines where
  /-- Instanced SDF quads (fills, strokes, circles, axis-aligned lines). -/
  quad : GraphicsPipeline
  /-- Indexed CPU-tessellated triangles (the SDL-parity fallback). -/
  mesh : GraphicsPipeline
  /-- Indexed glyph-atlas triangles. -/
  glyph : GraphicsPipeline

/-- Compile the MSL shaders and build the three pipelines against `target`
(the swapchain's native format for on-screen rendering; rgba8 for offscreen
targets later). Shaders are released after pipeline creation (probe-verified
safe); the returned pipelines must stay reachable while bound. -/
def Pipelines.create (dev : Device) (target : TextureFormat) : IO Pipelines := do
  let shader (src entry : String) (stage : ShaderStage) (samplers : UInt32 := 0)
      (uniforms : UInt32 := 0) : IO Shader :=
    dev.createShader
      { code := src.toUTF8, entrypoint := entry, format := .msl, stage
        numSamplers := samplers, numUniformBuffers := uniforms }
  let targetInfo : GraphicsPipelineTargetInfo :=
    { colorTargetDescriptions := #[{ format := target, blendState := premulBlend }] }
  -- quad: one instance-rate vertex buffer, 9 float4 attributes
  let quadVs ← shader quadMsl "quad_vertex" .vertex (uniforms := 1)
  let quadFs ← shader quadMsl "quad_fragment" .fragment
  let quad ← dev.createGraphicsPipeline
    { vertexShader := quadVs, fragmentShader := quadFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat quadStride, inputRate := .instance }]
          vertexAttributes := (Array.range 9).map fun i =>
            { location := UInt32.ofNat i, bufferSlot := 0, format := .float4
              offset := UInt32.ofNat (i * 16) } }
      primitiveType := .triangleStrip
      targetInfo }
  quadVs.release
  quadFs.release
  -- mesh: pos float2 @0, color float4 @8
  let meshVs ← shader meshMsl "mesh_vertex" .vertex (uniforms := 1)
  let meshFs ← shader meshMsl "mesh_fragment" .fragment
  let mesh ← dev.createGraphicsPipeline
    { vertexShader := meshVs, fragmentShader := meshFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat meshVertexStride }]
          vertexAttributes :=
            #[{ location := 0, bufferSlot := 0, format := .float2, offset := 0 },
              { location := 1, bufferSlot := 0, format := .float4, offset := 8 }] }
      targetInfo }
  meshVs.release
  meshFs.release
  -- glyph: pos float2 @0, uv float2 @8, color float4 @16
  let glyphVs ← shader glyphMsl "tex_vertex" .vertex (uniforms := 1)
  let glyphFs ← shader glyphMsl "tex_fragment" .fragment (samplers := 1)
  let glyph ← dev.createGraphicsPipeline
    { vertexShader := glyphVs, fragmentShader := glyphFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat texVertexStride }]
          vertexAttributes :=
            #[{ location := 0, bufferSlot := 0, format := .float2, offset := 0 },
              { location := 1, bufferSlot := 0, format := .float2, offset := 8 },
              { location := 2, bufferSlot := 0, format := .float4, offset := 16 }] }
      targetInfo }
  glyphVs.release
  glyphFs.release
  return { quad := quad, mesh := mesh, glyph := glyph }

end Compose.Draw.Gpu
