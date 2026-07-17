#version 450
// Twin of `stretch_fragment` (stretchMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// the layer composite with the AOSP/Flutter overscroll warp
// (Gpu.Sdf.stretchPosUp / stretchPos) applied to the UV before sampling.
// UV normalizes by the content's extent in the pooled texture, warps, clamps
// to the CONTENT rect (never the pooled texture's slack), and maps back.
// Varyings mirror tex.vert.

layout(set = 2, binding = 0) uniform sampler2D layer;

layout(set = 3, binding = 0, std140) uniform StretchParams {
  vec2 stretch;  // signed per-axis intensity (positive pins the start edge)
  vec2 uvScale;  // the content's UV extent in the pooled texture
};

layout(location = 0) in vec2 uv;
layout(location = 1) in vec4 color;

layout(location = 0) out vec4 fragColor;

// Gpu.Sdf.stretchPosUp — 0.7 = Foundation.stretchInterpolationStrength
float stretch_pos_up(float p, float s) {
  return 1.0 / (1.0 + s) - (1.0 - p) / (1.0 + s * (1.0 - 0.7 * p));
}

// Gpu.Sdf.stretchPos
float stretch_pos(float p, float s) {
  if (s > 0.0) return stretch_pos_up(p, s);
  if (s < 0.0) return 1.0 - stretch_pos_up(1.0 - p, -s);
  return p;
}

void main() {
  vec2 np = uv / uvScale;
  vec2 q = vec2(stretch_pos(np.x, stretch.x), stretch_pos(np.y, stretch.y));
  vec2 suv = clamp(q, 0.0, 1.0) * uvScale;
  fragColor = texture(layer, suv) * color.a;
}
