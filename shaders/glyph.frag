#version 450
// Twin of `tex_fragment` (glyphMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// atlas texel × run color, premultiplied on output.
// Varyings mirror tex.vert.

layout(set = 2, binding = 0) uniform sampler2D atlas;

layout(location = 0) in vec2 uv;
layout(location = 1) in vec4 color;

layout(location = 0) out vec4 fragColor;

void main() {
  vec4 t = texture(atlas, uv);
  vec4 c = t * color;
  fragColor = vec4(c.rgb * c.a, c.a);
}
