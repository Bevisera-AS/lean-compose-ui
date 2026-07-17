#version 450
// Twin of `shadow_fragment` (shadowMsl) in Compose/Ui/Draw/Gpu/Shaders.lean.
// erf4/gauss/shadow_x/the quadrature loop are twins of
// Gpu.Sdf.erf4/gaussian/shadowX/shadow.
// The varying block below must stay textually mirrored in shadow.vert.

float erf4(float x) {                                   // Gpu.Sdf.erf4
  float s = x < 0.0 ? -1.0 : 1.0;
  float a = abs(x);
  float t = 1.0 + (0.278393 + (0.230389 + 0.078108 * (a * a)) * a) * a;
  float t2 = t * t;
  return s - s / (t2 * t2);
}

float gauss(float x, float sigma) {                     // Gpu.Sdf.gaussian
  return exp(-(x * x) / (2.0 * sigma * sigma)) / (2.50662827463 * sigma);
}

float shadow_x(float x, float y, float sigma, float corner,
               float halfW, float halfH) {              // Gpu.Sdf.shadowX
  float delta = min(halfH - corner - abs(y), 0.0);
  float curved = halfW - corner + sqrt(max(corner * corner - delta * delta, 0.0));
  float lo = 0.5 + 0.5 * erf4((x - curved) * (0.70710678 / sigma));
  float hi = 0.5 + 0.5 * erf4((x + curved) * (0.70710678 / sigma));
  return hi - lo;
}

layout(location = 0) in vec2 world;
layout(location = 1) flat in vec4 bounds;
layout(location = 2) flat in vec4 color;
layout(location = 3) flat in vec2 params;

layout(location = 0) out vec4 fragColor;

void main() {
  float sigma = params.x;
  float corner = params.y;
  vec2 hs = bounds.zw * 0.5;
  vec2 pt = world - (bounds.xy + hs);
  float low = pt.y - hs.y;
  float high = pt.y + hs.y;
  float start = clamp(-3.0 * sigma, low, high);
  float stop = clamp(3.0 * sigma, low, high);
  float step = (stop - start) / 4.0;
  float y = start + step * 0.5;
  float value = 0.0;
  for (int i = 0; i < 4; i++) {                         // Gpu.Sdf.shadow
    value += shadow_x(pt.x, pt.y - y, sigma, corner, hs.x, hs.y)
               * gauss(y, sigma) * step;
    y += step;
  }
  float cov = value;
  vec4 src = color;
  fragColor = vec4(src.rgb * src.a * cov, src.a * cov);
}
