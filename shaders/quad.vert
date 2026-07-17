#version 450
// Twin of `quad_vertex` (quadMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.
// The varying block below must stay textually mirrored in quad.frag —
// glslc does not cross-check stage interfaces.
#include "prelude.glsl"

layout(set = 1, binding = 0, std140) uniform Globals { vec2 viewport; };

layout(location = 0) in vec4 inBounds;
layout(location = 1) in vec4 inRadii;
layout(location = 2) in vec4 inBg0;
layout(location = 3) in vec4 inBg1;
layout(location = 4) in vec4 inGradient;
layout(location = 5) in vec4 inBorder;
layout(location = 6) in vec4 inBorderW;
layout(location = 7) in vec4 inClipBounds;
layout(location = 8) in vec4 inClipRadii;

layout(location = 0) out vec2 world;
layout(location = 1) flat out vec4 bounds;
layout(location = 2) flat out vec4 radii;
layout(location = 3) flat out vec4 bg0;
layout(location = 4) flat out vec4 bg1;
layout(location = 5) flat out vec4 gradient;
layout(location = 6) flat out vec4 border;
layout(location = 7) flat out float borderW;
layout(location = 8) flat out float gradKind;
layout(location = 9) flat out vec4 clipBounds;
layout(location = 10) flat out vec4 clipRadii;

void main() {
  float inflate = inBorderW.x * 0.5 + 1.0;
  uint vid = uint(gl_VertexIndex);  // firstVertex is always 0 (SDL_gpu.h builtin caveat)
  vec2 corner = vec2(float(vid & 1u), float(vid >> 1u));
  vec2 p = inBounds.xy - inflate + corner * (inBounds.zw + 2.0 * inflate);
  gl_Position = to_ndc(p, viewport);
  world = p;
  bounds = inBounds;
  radii = inRadii;
  bg0 = inBg0;
  bg1 = inBg1;
  gradient = inGradient;
  border = inBorder;
  borderW = inBorderW.x;
  gradKind = inBorderW.y;
  clipBounds = inClipBounds;
  clipRadii = inClipRadii;
}
