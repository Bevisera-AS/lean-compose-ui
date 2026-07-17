#version 450
// Twin of `quad_fragment` (quadMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.
// The varying block below must stay textually mirrored in quad.vert.
#include "prelude.glsl"

float saturate(float x) { return clamp(x, 0.0, 1.0); }  // Gpu.Sdf.saturate

float ign(vec2 p) {                                     // Gpu.Sdf.ign
  return fract(52.9829189 * fract(0.06711056 * p.x + 0.00583715 * p.y));
}

layout(location = 0) in vec2 world;
layout(location = 1) flat in vec4 bounds;
layout(location = 2) flat in vec4 radii;
layout(location = 3) flat in vec4 bg0;
layout(location = 4) flat in vec4 bg1;
layout(location = 5) flat in vec4 gradient;
layout(location = 6) flat in vec4 border;
layout(location = 7) flat in float borderW;
layout(location = 8) flat in float gradKind;
layout(location = 9) flat in vec4 clipBounds;
layout(location = 10) flat in vec4 clipRadii;

layout(location = 0) out vec4 fragColor;

void main() {
  float sdf = rrect_sdf(world, bounds, radii);
  float clip = saturate(0.5 - rrect_sdf(world, clipBounds, clipRadii));
  vec4 src;
  float cov;
  if (borderW > 0.0) {
    src = border;
    cov = saturate(0.5 - (abs(sdf) - borderW * 0.5));
  } else {
    float t;
    if (gradKind < 0.5) {          // linear
      t = saturate(dot(world - gradient.xy, gradient.zw));
    } else if (gradKind < 1.5) {   // radial (Gpu.Sdf.radialT)
      t = saturate(length(world - gradient.xy) * gradient.z + gradient.w);
    } else {                       // sweep (Gpu.Sdf.sweepT)
      vec2 d = world - gradient.xy;
      t = fract((atan(d.y, d.x) - gradient.z) * 0.15915494309189533577);
    }
    src = mix(bg0, bg1, t);
    if (any(notEqual(bg0, bg1))) { // dither gradient fills only (Gpu.Sdf.ign)
      src.rgb = clamp(src.rgb + (ign(gl_FragCoord.xy) - 0.5) * (1.0 / 255.0), 0.0, 1.0);
    }
    cov = saturate(0.5 - sdf);
  }
  cov *= clip;
  fragColor = vec4(src.rgb * src.a * cov, src.a * cov);
}
