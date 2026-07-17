#version 450
// Twin of `layer_fragment` (layerMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// the sampled texel is already premultiplied — scale all four channels by
// the group alpha and do NOT re-premultiply.
// Varyings mirror tex.vert.

layout(set = 2, binding = 0) uniform sampler2D layer;

layout(location = 0) in vec2 uv;
layout(location = 1) in vec4 color;

layout(location = 0) out vec4 fragColor;

void main() {
  fragColor = texture(layer, uv) * color.a;
}
