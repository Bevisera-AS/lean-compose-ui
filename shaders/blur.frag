#version 450
// Twin of `blur_fragment` (blurMsl) in Compose/Ui/Draw/Gpu/Shaders.lean:
// one direction of a separable Gaussian; taps pair up through the linear
// sampler; accumulates premultiplied texels, normalizes by the accumulated
// weight. Varyings mirror blur.vert.

layout(set = 2, binding = 0) uniform sampler2D src;

layout(set = 3, binding = 0, std140) uniform BlurParams {
  vec2 dir;
  float sigma;
  float taps;
};

layout(location = 0) in vec2 uv;

layout(location = 0) out vec4 fragColor;

void main() {
  vec4 acc = texture(src, uv);
  float wsum = 1.0;
  float inv2s2 = 1.0 / (2.0 * sigma * sigma);
  int n = int(taps);
  for (int i = 1; i <= n; i += 2) {
    float w0 = exp(-float(i) * float(i) * inv2s2);        // Gpu.Sdf.blurWeight
    float w1 = exp(-float(i + 1) * float(i + 1) * inv2s2);
    float w = w0 + w1;
    float off = float(i) + w1 / w;                        // Gpu.Sdf.blurTapOffset
    acc += (texture(src, uv + dir * off)
          + texture(src, uv - dir * off)) * w;
    wsum += 2.0 * w;
  }
  fragColor = acc / wsum;
}
