module

public import Compose.Ui.Draw.Gpu.Instance
public meta import Compose.Ui.Draw.Gpu.Instance
public import Compose.Ui.Draw.Gpu.SpirvBlobs
public meta import Compose.Ui.Draw.Gpu.SpirvBlobs
public import Sdl
public meta import Sdl

public section

/-!
# GPU shaders & pipelines (`Compose/Ui/Draw/Gpu/Shaders.lean`)

The MSL shader sources (runtime-compiled — probe-verified the Metal backend
accepts MSL source) and the graphics pipelines. Each MSL shader has a GLSL
dialect twin in `shaders/` compiled to SPIR-V and embedded via
`Gpu/SpirvBlobs.lean` (`scripts/gen-shaders.sh`) — `Pipelines.create` picks
the dialect the device accepts (Metal → MSL, Vulkan → SPIR-V). Keep the two
dialects in lockstep; both cite the `#guard`-tested formula twins in
`Gpu/Sdf.lean`. The seven pipelines:

- **quad**: instanced unit triangle strips (corners from `vertex_id`, all
  attributes instance-rate at `quadStride`), SDF fill/stroke coverage plus a
  rounded clip mask. The SDF/coverage formulas are twins of the `#guard`-tested
  Lean functions in `Gpu/Sdf.lean` (cited by name below).
- **shadow**: instanced quads evaluating Evan Wallace's analytic Gaussian
  rounded-rect shadow (twin of `Gpu.Sdf.shadow`/`shadowX`/`erf4`/`gaussian`).
- **mesh**: indexed triangles from the CPU tessellator (SDL-parity fallback).
- **glyph**: indexed textured triangles over SDL_ttf's GPU glyph atlas.
- **layer**: indexed textured triangles compositing an offscreen layer — the
  texel is already premultiplied, so the fragment just scales by the group
  alpha carried in the vertex color.
- **blur**: one direction of a separable Gaussian over a layer texture
  (`LayerEffect.blur`) — vertex-buffer-free, geometry from a vertex uniform,
  kernel parameters from a fragment uniform.
- **stretch**: the layer composite with the Android-12 overscroll warp
  (`LayerEffect.stretch`, twin of `Gpu.Sdf.stretchPos`) applied to the UV
  before sampling — intensity and content UV extent from a fragment uniform
  pushed per composite draw.

All pipelines blend premultiplied (`one / oneMinusSrcAlpha`) except `blur`,
which overwrites its cleared target; colors travel non-premultiplied in
vertex data and fragments premultiply after coverage (except `layer` and
`blur`, whose inputs are premultiplied), so interpolation matches the SDL
backend's non-premultiplied vertex colors. Uniforms: one 16-byte
`Globals { float2 viewport }` at vertex `[[buffer(0)]]`, pushed once per
render pass (layer passes remap NDC to their texture's extent); the blur
passes push their own `BlurVert`/`BlurParams` pair instead.
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
`Gpu.Sdf.coverage`), both masked by the rounded clip. The gradient fraction
`t` is selected by `gradKind` (0 linear, 1 radial, 2 sweep — twins
`Gpu.Sdf.radialT`/`sweepT`), and gradient fills (`bg0 ≠ bg1`) are dithered
with interleaved gradient noise (`Gpu.Sdf.ign`, ±½ of an 8-bit step before
quantization) — solid fills stay bit-stable. -/
private def quadMsl : String := mslPrelude ++ "
static inline float ign(float2 p) {
  return fract(52.9829189 * fract(0.06711056 * p.x + 0.00583715 * p.y));
}

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
  float  gradKind   [[flat]];
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
  out.gradKind = in.borderW.y;
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
    float t;
    if (in.gradKind < 0.5) {          // linear
      t = saturate(dot(in.world - in.gradient.xy, in.gradient.zw));
    } else if (in.gradKind < 1.5) {   // radial (Gpu.Sdf.radialT)
      t = saturate(length(in.world - in.gradient.xy) * in.gradient.z + in.gradient.w);
    } else {                          // sweep (Gpu.Sdf.sweepT)
      float2 d = in.world - in.gradient.xy;
      t = fract((atan2(d.y, d.x) - in.gradient.z) * 0.15915494309189533577);
    }
    src = mix(in.bg0, in.bg1, t);
    if (any(in.bg0 != in.bg1)) {      // dither gradient fills only (Gpu.Sdf.ign)
      src.rgb = saturate(src.rgb + (ign(in.pos.xy) - 0.5) * (1.0 / 255.0));
    }
    cov = saturate(0.5 - sdf);
  }
  cov *= clip;
  return float4(src.rgb * src.a * cov, src.a * cov);
}
"

/-- The shadow pipeline's MSL: an instanced quad inflated `3σ + 1` px around
the shadow-casting rect, whose fragment evaluates the analytic Gaussian
rounded-rect shadow — `erf4`/`gauss`/`shadow_x`/the quadrature loop are twins
of `Gpu.Sdf.erf4`/`gaussian`/`shadowX`/`shadow`. -/
private def shadowMsl : String := mslPrelude ++ "
static inline float erf4(float x) {
  float s = x < 0.0 ? -1.0 : 1.0;
  float a = abs(x);
  float t = 1.0 + (0.278393 + (0.230389 + 0.078108 * (a * a)) * a) * a;
  float t2 = t * t;
  return s - s / (t2 * t2);
}

static inline float gauss(float x, float sigma) {
  return exp(-(x * x) / (2.0 * sigma * sigma)) / (2.50662827463 * sigma);
}

static inline float shadow_x(float x, float y, float sigma, float corner,
                             float halfW, float halfH) {
  float delta = min(halfH - corner - abs(y), 0.0);
  float curved = halfW - corner + sqrt(max(corner * corner - delta * delta, 0.0));
  float lo = 0.5 + 0.5 * erf4((x - curved) * (0.70710678 / sigma));
  float hi = 0.5 + 0.5 * erf4((x + curved) * (0.70710678 / sigma));
  return hi - lo;
}

struct ShadowIn {
  float4 bounds [[attribute(0)]];
  float4 color  [[attribute(1)]];
  float4 params [[attribute(2)]];
};

struct ShadowOut {
  float4 pos [[position]];
  float2 world;
  float4 bounds [[flat]];
  float4 color  [[flat]];
  float2 params [[flat]];
};

vertex ShadowOut shadow_vertex(ShadowIn in [[stage_in]], uint vid [[vertex_id]],
                               constant Globals& g [[buffer(0)]]) {
  float inflate = in.params.x * 3.0 + 1.0;
  float2 corner = float2(float(vid & 1u), float(vid >> 1u));
  float2 p = in.bounds.xy - inflate + corner * (in.bounds.zw + 2.0 * inflate);
  ShadowOut out;
  out.pos = to_ndc(p, g.viewport);
  out.world = p;
  out.bounds = in.bounds;
  out.color = in.color;
  out.params = in.params.xy;
  return out;
}

fragment float4 shadow_fragment(ShadowOut in [[stage_in]]) {
  float sigma = in.params.x;
  float corner = in.params.y;
  float2 hs = in.bounds.zw * 0.5;
  float2 pt = in.world - (in.bounds.xy + hs);
  float low = pt.y - hs.y;
  float high = pt.y + hs.y;
  float start = clamp(-3.0 * sigma, low, high);
  float stop = clamp(3.0 * sigma, low, high);
  float step = (stop - start) / 4.0;
  float y = start + step * 0.5;
  float value = 0.0;
  for (int i = 0; i < 4; i++) {
    value += shadow_x(pt.x, pt.y - y, sigma, corner, hs.x, hs.y)
               * gauss(y, sigma) * step;
    y += step;
  }
  float cov = value;
  float4 src = in.color;
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

/-- The layer-composite pipeline's MSL: same vertex layout as the glyph
pipeline, but the sampled texel is an offscreen layer's *premultiplied*
pixels — the fragment scales all four channels by the group alpha
(`color.a`) and must not re-premultiply. The `LayerClip` fragment uniform
(pushed per composite draw, `packLayerClip`) masks the composite against
the record-site rounded clip — the huge-rect sentinel when unmasked — with
the quad fragment's exact coverage term; `in.pos` (`gl_FragCoord` in the
GLSL twin) supplies the pass-coordinate pixel position. -/
private def layerMsl : String := mslPrelude ++ "
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

struct LayerClip {
  float4 bounds;
  float4 radii;
};

vertex TexOut layer_vertex(TexIn in [[stage_in]],
                           constant Globals& g [[buffer(0)]]) {
  TexOut out;
  out.pos = to_ndc(in.pos, g.viewport);
  out.uv = in.uv;
  out.color = in.color;
  return out;
}

fragment float4 layer_fragment(TexOut in [[stage_in]],
                               constant LayerClip& lc [[buffer(0)]],
                               texture2d<float> layer [[texture(0)]],
                               sampler smp [[sampler(0)]]) {
  float clip = saturate(0.5 - rrect_sdf(in.pos.xy, lc.bounds, lc.radii));
  return layer.sample(smp, in.uv) * (in.color.a * clip);
}
"

/-- The stretch-composite pipeline's MSL: the layer pipeline's vertex layout
and premultiplied-composite fragment, with the AOSP/Flutter overscroll warp
(twins `Gpu.Sdf.stretchPosUp`/`stretchPos`; the `0.7` is
`Foundation.stretchInterpolationStrength`) applied to the UV before sampling.
The fragment normalizes UV by the content's extent in the pooled texture
(`uvScale`), warps, clamps to the **content** rect — never the pooled
texture's edge, whose slack holds transparent or stale texels — and maps
back. `StretchParams` arrives via `pushFragmentUniformData` before each
composite draw. -/
private def stretchMsl : String := mslPrelude ++ "
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

vertex TexOut stretch_vertex(TexIn in [[stage_in]],
                             constant Globals& g [[buffer(0)]]) {
  TexOut out;
  out.pos = to_ndc(in.pos, g.viewport);
  out.uv = in.uv;
  out.color = in.color;
  return out;
}

struct StretchParams {
  float2 stretch;
  float2 uvScale;
};

// Gpu.Sdf.stretchPosUp — 0.7 = Foundation.stretchInterpolationStrength
static inline float stretch_pos_up(float p, float s) {
  return 1.0 / (1.0 + s) - (1.0 - p) / (1.0 + s * (1.0 - 0.7 * p));
}

// Gpu.Sdf.stretchPos
static inline float stretch_pos(float p, float s) {
  if (s > 0.0) return stretch_pos_up(p, s);
  if (s < 0.0) return 1.0 - stretch_pos_up(1.0 - p, -s);
  return p;
}

fragment float4 stretch_fragment(TexOut in [[stage_in]],
                                 constant StretchParams& sp [[buffer(0)]],
                                 texture2d<float> layer [[texture(0)]],
                                 sampler smp [[sampler(0)]]) {
  float2 np = in.uv / sp.uvScale;
  float2 q = float2(stretch_pos(np.x, sp.stretch.x),
                    stretch_pos(np.y, sp.stretch.y));
  float2 suv = clamp(q, 0.0, 1.0) * sp.uvScale;
  return layer.sample(smp, suv) * in.color.a;
}
"

/-- The blur pipeline's MSL: a **vertex-buffer-free** full-region quad
(corners from `vertex_id`, geometry entirely from the `BlurVert` vertex
uniform — the region's extent in the target plus the source texture's UV
scale) whose fragment runs one direction of a separable Gaussian. Taps pair
up through the linear sampler (one bilinear fetch at
`i + w(i+1)/(w(i)+w(i+1))` weighs texels `i` and `i + 1` exactly — twins
`Gpu.Sdf.blurWeight`/`blurTapOffset`), accumulating premultiplied texels and
normalizing by the accumulated weight, so the discrete kernel always sums to
one. `BlurParams` arrives via `pushFragmentUniformData` (fragment
`[[buffer(0)]]`, probe-verified): `dir` is one texel step in UV space along
the pass direction, `taps` the per-side texel reach (`⌈3σ⌉`). The pipeline
does not blend (it overwrites its cleared target). -/
private def blurMsl : String := mslPrelude ++ "
struct BlurVert {
  float2 viewport;
  float2 extent;
  float2 uvScale;
  float2 pad;
};

struct BlurOut {
  float4 pos [[position]];
  float2 uv;
};

vertex BlurOut blur_vertex(uint vid [[vertex_id]],
                           constant BlurVert& g [[buffer(0)]]) {
  float2 corner = float2(float(vid & 1u), float(vid >> 1u));
  BlurOut out;
  out.pos = to_ndc(corner * g.extent, g.viewport);
  out.uv = corner * g.uvScale;
  return out;
}

struct BlurParams {
  float2 dir;
  float sigma;
  float taps;
};

fragment float4 blur_fragment(BlurOut in [[stage_in]],
                              constant BlurParams& p [[buffer(0)]],
                              texture2d<float> src [[texture(0)]],
                              sampler smp [[sampler(0)]]) {
  float4 acc = src.sample(smp, in.uv);
  float wsum = 1.0;
  float inv2s2 = 1.0 / (2.0 * p.sigma * p.sigma);
  int n = int(p.taps);
  for (int i = 1; i <= n; i += 2) {
    float w0 = exp(-float(i) * float(i) * inv2s2);        // Gpu.Sdf.blurWeight
    float w1 = exp(-float(i + 1) * float(i + 1) * inv2s2);
    float w = w0 + w1;
    float off = float(i) + w1 / w;                        // Gpu.Sdf.blurTapOffset
    acc += (src.sample(smp, in.uv + p.dir * off)
          + src.sample(smp, in.uv - p.dir * off)) * w;
    wsum += 2.0 * w;
  }
  return acc / wsum;
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

/-- The 32-byte `BlurVert` vertex uniform: target viewport, region extent,
source UV scale (+ pad). -/
def packBlurVert (viewportW viewportH extentW extentH uvW uvH : Float32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 32
  for v in [viewportW, viewportH, extentW, extentH, uvW, uvH, 0, 0] do
    b := pushF32 b v
  return b

/-- The 16-byte `BlurParams` fragment uniform: one-texel UV step along the
pass direction, σ, and the per-side texel reach. -/
def packBlurParams (dirU dirV sigma taps : Float32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 16
  for v in [dirU, dirV, sigma, taps] do
    b := pushF32 b v
  return b

/-- The 16-byte `StretchParams` fragment uniform: the signed per-axis
stretch intensity and the content's UV extent in the pooled texture. -/
def packStretchParams (sx sy uMax vMax : Float32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 16
  for v in [sx, sy, uMax, vMax] do
    b := pushF32 b v
  return b

/-- The 32-byte `LayerClip` fragment uniform (two std140 `vec4`s): the
composite's rounded-clip bounds as `(x, y, w, h)` plus per-corner radii
`(tl, tr, br, bl)` in the compositing pass's px, elliptical corners
degrading to the x radius like every quad mask. `none` packs the huge-rect
sentinel (the `QuadInstance` unmasked-clip convention) — coverage 1
everywhere a composite can reach. -/
def packLayerClip (rr : Option Compose.RoundRect) : ByteArray := Id.run do
  let vals : List Float32 := match rr with
    | some rr =>
      let rr := rr.normalize
      [rr.rect.left, rr.rect.top, rr.rect.width, rr.rect.height,
       rr.topLeft.x, rr.topRight.x, rr.bottomRight.x, rr.bottomLeft.x]
    | none => [-1e8, -1e8, 2e8, 2e8, 0, 0, 0, 0]
  let mut b := ByteArray.emptyWithCapacity 32
  for v in vals do
    b := pushF32 b v
  return b

#guard (packBlurVert 256 128 80 40 0.3125 0.3125).size == 32
#guard (packBlurParams 0.00390625 0 4 12).size == 16
#guard (packStretchParams 0.032 0 0.8 0.625).size == 16
#guard (packLayerClip none).size == 32
#guard (packLayerClip (some (.circular ⟨10, 20, 50, 60⟩ 8))).size == 32
-- Bounds pack as (x, y, w, h); the sentinel starts with the huge rect.
#guard (packLayerClip (some (.circular ⟨10, 20, 50, 60⟩ 8)))
        == (pushF32 (pushF32 (pushF32 (pushF32 (pushF32 (pushF32 (pushF32 (pushF32
              ByteArray.empty 10) 20) 40) 40) 8) 8) 8) 8)
#guard (packLayerClip none).extract 0 16
        == (pushF32 (pushF32 (pushF32 (pushF32 ByteArray.empty (-1e8)) (-1e8)) 2e8) 2e8)

/-- Premultiplied-alpha blending — the one blend state every pipeline uses. -/
private def premulBlend : ColorTargetBlendState :=
  { srcColorBlendfactor := .one, dstColorBlendfactor := .oneMinusSrcAlpha
    colorBlendOp := .add
    srcAlphaBlendfactor := .one, dstAlphaBlendfactor := .oneMinusSrcAlpha
    alphaBlendOp := .add
    enableBlend := true }

/-- The pipeline set for one color-target format. -/
structure Pipelines where
  /-- Instanced SDF quads (fills, strokes, circles, axis-aligned lines). -/
  quad : GraphicsPipeline
  /-- Instanced analytic Gaussian shadows. -/
  shadow : GraphicsPipeline
  /-- Indexed CPU-tessellated triangles (the SDL-parity fallback). -/
  mesh : GraphicsPipeline
  /-- Indexed glyph-atlas triangles. -/
  glyph : GraphicsPipeline
  /-- Indexed premultiplied layer-composite quads. -/
  layer : GraphicsPipeline
  /-- Vertex-buffer-free separable Gaussian blur (one direction per pass,
  no blending — overwrites its cleared target). -/
  blur : GraphicsPipeline
  /-- The layer composite with the overscroll stretch warp on its UVs. -/
  stretch : GraphicsPipeline

/-- Build the seven pipelines against `target` (the swapchain's native format
for on-screen rendering; rgba8 for offscreen targets later), compiling the
shader dialect the device accepts: MSL source where available (Metal —
desktop path unchanged), else the embedded SPIR-V blobs from
`Gpu/SpirvBlobs.lean` (Vulkan: Android, or MoltenVK via
`COMPOSE_GPU_DRIVER=vulkan`). Shaders are released after pipeline creation
(probe-verified safe); the returned pipelines must stay reachable while
bound. -/
def Pipelines.create (dev : Device) (target : TextureFormat) : IO Pipelines := do
  let formats ← dev.getShaderFormats
  let useSpirv := !formats.has .msl && formats.has .spirv
  if !formats.has .msl && !formats.has .spirv then
    throw <| IO.userError
      s!"GPU device supports neither MSL nor SPIR-V shaders (formats {formats.val})"
  let shader (msl : String) (spv : ByteArray) (entry : String) (stage : ShaderStage)
      (samplers : UInt32 := 0) (uniforms : UInt32 := 0) : IO Shader :=
    if useSpirv then
      dev.createShader
        { code := spv, entrypoint := "main", format := .spirv, stage
          numSamplers := samplers, numUniformBuffers := uniforms }
    else
      dev.createShader
        { code := msl.toUTF8, entrypoint := entry, format := .msl, stage
          numSamplers := samplers, numUniformBuffers := uniforms }
  let targetInfo : GraphicsPipelineTargetInfo :=
    { colorTargetDescriptions := #[{ format := target, blendState := premulBlend }] }
  -- quad: one instance-rate vertex buffer, 9 float4 attributes
  let quadVs ← shader quadMsl quadVertSpv "quad_vertex" .vertex (uniforms := 1)
  let quadFs ← shader quadMsl quadFragSpv "quad_fragment" .fragment
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
  -- shadow: one instance-rate vertex buffer, 3 float4 attributes
  let shadowVs ← shader shadowMsl shadowVertSpv "shadow_vertex" .vertex (uniforms := 1)
  let shadowFs ← shader shadowMsl shadowFragSpv "shadow_fragment" .fragment
  let shadow ← dev.createGraphicsPipeline
    { vertexShader := shadowVs, fragmentShader := shadowFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat shadowStride, inputRate := .instance }]
          vertexAttributes := (Array.range 3).map fun i =>
            { location := UInt32.ofNat i, bufferSlot := 0, format := .float4
              offset := UInt32.ofNat (i * 16) } }
      primitiveType := .triangleStrip
      targetInfo }
  shadowVs.release
  shadowFs.release
  -- mesh: pos float2 @0, color float4 @8
  let meshVs ← shader meshMsl meshVertSpv "mesh_vertex" .vertex (uniforms := 1)
  let meshFs ← shader meshMsl meshFragSpv "mesh_fragment" .fragment
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
  -- texVertSpv serves both glyph and layer (the MSL vertex twins are
  -- byte-identical bodies; SPIR-V entrypoints are all `main`)
  let glyphVs ← shader glyphMsl texVertSpv "tex_vertex" .vertex (uniforms := 1)
  let glyphFs ← shader glyphMsl glyphFragSpv "tex_fragment" .fragment (samplers := 1)
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
  -- layer: the glyph vertex layout with the premultiplied-composite fragment
  -- (its `LayerClip` fragment uniform is pushed per composite/image draw)
  let layerVs ← shader layerMsl texVertSpv "layer_vertex" .vertex (uniforms := 1)
  let layerFs ← shader layerMsl layerFragSpv "layer_fragment" .fragment
    (samplers := 1) (uniforms := 1)
  let layer ← dev.createGraphicsPipeline
    { vertexShader := layerVs, fragmentShader := layerFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat texVertexStride }]
          vertexAttributes :=
            #[{ location := 0, bufferSlot := 0, format := .float2, offset := 0 },
              { location := 1, bufferSlot := 0, format := .float2, offset := 8 },
              { location := 2, bufferSlot := 0, format := .float4, offset := 16 }] }
      targetInfo }
  layerVs.release
  layerFs.release
  -- stretch: the layer vertex layout + the UV-warping composite fragment
  -- (its `StretchParams` fragment uniform is pushed per composite draw)
  let stretchVs ← shader stretchMsl texVertSpv "stretch_vertex" .vertex (uniforms := 1)
  let stretchFs ← shader stretchMsl stretchFragSpv "stretch_fragment" .fragment
    (samplers := 1) (uniforms := 1)
  let stretch ← dev.createGraphicsPipeline
    { vertexShader := stretchVs, fragmentShader := stretchFs
      vertexInputState :=
        { vertexBufferDescriptions :=
            #[{ slot := 0, pitch := UInt32.ofNat texVertexStride }]
          vertexAttributes :=
            #[{ location := 0, bufferSlot := 0, format := .float2, offset := 0 },
              { location := 1, bufferSlot := 0, format := .float2, offset := 8 },
              { location := 2, bufferSlot := 0, format := .float4, offset := 16 }] }
      targetInfo }
  stretchVs.release
  stretchFs.release
  -- blur: no vertex buffers (corners from `vertex_id`; geometry from the
  -- vertex uniform), fragment uniform + sampler, blending off (the pass
  -- overwrites its cleared target).
  let blurVs ← shader blurMsl blurVertSpv "blur_vertex" .vertex (uniforms := 1)
  let blurFs ← shader blurMsl blurFragSpv "blur_fragment" .fragment (samplers := 1) (uniforms := 1)
  let blur ← dev.createGraphicsPipeline
    { vertexShader := blurVs, fragmentShader := blurFs
      primitiveType := .triangleStrip
      targetInfo := { colorTargetDescriptions := #[{ format := target }] } }
  blurVs.release
  blurFs.release
  return { quad := quad, shadow := shadow, mesh := mesh, glyph := glyph
           layer := layer, blur := blur, stretch := stretch }

end Compose.Draw.Gpu

end
