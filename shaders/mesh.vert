#version 450
// Twin of `mesh_vertex` (meshMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.
#include "prelude.glsl"

layout(set = 1, binding = 0, std140) uniform Globals { vec2 viewport; };

layout(location = 0) in vec2 inPos;
layout(location = 1) in vec4 inColor;

layout(location = 0) out vec4 color;

void main() {
  gl_Position = to_ndc(inPos, viewport);
  color = inColor;
}
