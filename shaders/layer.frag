#version 450
// Twin of `layer_fragment` (layerMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// the sampled texel is already premultiplied — scale all four channels by
// the group alpha and do NOT re-premultiply. The LayerClip fragment uniform
// carries the composite's rounded clip as (x, y, w, h) bounds + per-corner
// radii in this pass's px (the huge-rect sentinel when unmasked — the
// QuadInstance clip convention); coverage multiplies exactly like the quad
// fragment's clip term. Varyings mirror tex.vert.
#include "prelude.glsl"

layout(set = 2, binding = 0) uniform sampler2D layer;

layout(set = 3, binding = 0, std140) uniform LayerClip {
  vec4 clipBounds;
  vec4 clipRadii;
};

layout(location = 0) in vec2 uv;
layout(location = 1) in vec4 color;

layout(location = 0) out vec4 fragColor;

void main() {
  float clip = clamp(0.5 - rrect_sdf(gl_FragCoord.xy, clipBounds, clipRadii), 0.0, 1.0);
  fragColor = texture(layer, uv) * (color.a * clip);
}
