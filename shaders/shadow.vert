#version 450
// Twin of `shadow_vertex` (shadowMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.
// The varying block below must stay textually mirrored in shadow.frag.
#include "prelude.glsl"

layout(set = 1, binding = 0, std140) uniform Globals { vec2 viewport; };

layout(location = 0) in vec4 inBounds;
layout(location = 1) in vec4 inColor;
layout(location = 2) in vec4 inParams;

layout(location = 0) out vec2 world;
layout(location = 1) flat out vec4 bounds;
layout(location = 2) flat out vec4 color;
layout(location = 3) flat out vec2 params;

void main() {
  float inflate = inParams.x * 3.0 + 1.0;
  uint vid = uint(gl_VertexIndex);
  vec2 corner = vec2(float(vid & 1u), float(vid >> 1u));
  vec2 p = inBounds.xy - inflate + corner * (inBounds.zw + 2.0 * inflate);
  gl_Position = to_ndc(p, viewport);
  world = p;
  bounds = inBounds;
  color = inColor;
  params = inParams.xy;
}
