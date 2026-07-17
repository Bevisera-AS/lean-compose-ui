#version 450
// Twin of `blur_vertex` (blurMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// vertex-buffer-free — corners from gl_VertexIndex, geometry entirely from
// the BlurVert vertex uniform.
#include "prelude.glsl"

layout(set = 1, binding = 0, std140) uniform BlurVert {
  vec2 viewport;
  vec2 extent;
  vec2 uvScale;
  vec2 pad;
};

layout(location = 0) out vec2 uv;

void main() {
  uint vid = uint(gl_VertexIndex);
  vec2 corner = vec2(float(vid & 1u), float(vid >> 1u));
  gl_Position = to_ndc(corner * extent, viewport);
  uv = corner * uvScale;
}
