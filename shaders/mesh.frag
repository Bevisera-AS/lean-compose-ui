#version 450
// Twin of `mesh_fragment` (meshMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.

layout(location = 0) in vec4 color;

layout(location = 0) out vec4 fragColor;

void main() {
  fragColor = vec4(color.rgb * color.a, color.a);
}
