#version 450
// Twin of `glass_fragment` (glassMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// the refractive backdrop-panel composite. Like layer.frag it samples a
// premultiplied texture, scales by the group alpha, and masks by the panel's
// rounded rect — but the sample position first displaces outward along the
// rect's SDF gradient by `refract_shift` (twins Gpu.Sdf.rrectGrad /
// Gpu.Sdf.refractShift: full `strength` px at the rim, zero `band` px
// inside), pulling blurred backdrop content inward like a lens. A positive
// `chroma` splits the red/blue channels ±chroma px along the same gradient,
// on the same falloff. UVs are reconstructed from gl_FragCoord via `uvMap`
// (uv = p·xy + zw) and clamped to `uvClamp` — the blurred region's real
// texels, never the pooled texture's slack. Varyings mirror tex.vert.
#include "prelude.glsl"

layout(set = 2, binding = 0) uniform sampler2D layer;

layout(set = 3, binding = 0, std140) uniform GlassParams {
  vec4 clipBounds;  // the panel rounded rect: mask AND refraction shape
  vec4 clipRadii;
  vec4 uvMap;       // xy = px→UV scale, zw = UV at the pass origin
  vec4 refr;        // x strength px, y band px (≥ 1), z chroma px, w unused
  vec4 uvClamp;     // xy min, zw max — the region's valid UV rect
};

layout(location = 0) in vec2 uv;
layout(location = 1) in vec4 color;

layout(location = 0) out vec4 fragColor;

// Gpu.Sdf.rrectGrad — the SDF's piecewise-analytic unit outward normal.
vec2 rrect_grad(vec2 p, vec4 bounds, vec4 radii) {
  vec2 hs = bounds.zw * 0.5;
  vec2 center = bounds.xy + hs;
  float r = pick_radius(p, center, radii);
  vec2 q = p - center;
  vec2 s = vec2(q.x >= 0.0 ? 1.0 : -1.0, q.y >= 0.0 ? 1.0 : -1.0);
  vec2 d = abs(q) - hs + r;
  if (d.x > 0.0 && d.y > 0.0) {
    return s * d / max(length(d), 1e-6);
  }
  return d.x > d.y ? vec2(s.x, 0.0) : vec2(0.0, s.y);
}

vec2 warp_uv(vec2 pw) {
  return clamp(pw * uvMap.xy + uvMap.zw, uvClamp.xy, uvClamp.zw);
}

void main() {
  vec2 p = gl_FragCoord.xy;
  float sdf = rrect_sdf(p, clipBounds, clipRadii);
  float clip = clamp(0.5 - sdf, 0.0, 1.0);
  vec2 g = rrect_grad(p, clipBounds, clipRadii);
  // Gpu.Sdf.refractShift — falloff shared by the bend and the chroma split.
  float fall = 1.0 - smoothstep(0.0, refr.y, -sdf);
  vec2 pw = p + g * (refr.x * fall);
  vec4 t = texture(layer, warp_uv(pw));
  float ch = refr.z * fall;
  if (ch > 0.0) {
    t.r = texture(layer, warp_uv(pw + g * ch)).r;
    t.b = texture(layer, warp_uv(pw - g * ch)).b;
  }
  fragColor = t * (color.a * clip);
}
