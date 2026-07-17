#version 450
// Twin of `tex_vertex`/`layer_vertex` in Compose/Ui/Draw/Gpu/Shaders.lean —
// the two MSL vertex functions are byte-identical bodies, so ONE SPIR-V blob
// serves both the glyph and layer pipelines (entrypoints are all "main").
#include "prelude.glsl"

layout(set = 1, binding = 0, std140) uniform Globals { vec2 viewport; };

layout(location = 0) in vec2 inPos;
layout(location = 1) in vec2 inUv;
layout(location = 2) in vec4 inColor;

layout(location = 0) out vec2 uv;
layout(location = 1) out vec4 color;

void main() {
  gl_Position = to_ndc(inPos, viewport);
  uv = inUv;
  color = inColor;
}
