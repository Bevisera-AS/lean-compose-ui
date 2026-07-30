// Shared GLSL prelude — twin of `mslPrelude` in Compose/Ui/Draw/Gpu/Shaders.lean.
// pick_radius / rrect_sdf are twins of Gpu.Sdf.pickRadius / Gpu.Sdf.rrectSdf
// (bounds as (x, y, w, h), radii as (tl, tr, br, bl)).

vec4 to_ndc(vec2 p, vec2 viewport) {
  return vec4(p / viewport * vec2(2.0, -2.0) + vec2(-1.0, 1.0), 0.0, 1.0);
}

float pick_radius(vec2 p, vec2 center, vec4 r) {
  return p.x < center.x ? (p.y < center.y ? r.x : r.w)
                        : (p.y < center.y ? r.y : r.z);
}

float rrect_sdf(vec2 p, vec4 bounds, vec4 radii) {
  vec2 hs = bounds.zw * 0.5;
  vec2 center = bounds.xy + hs;
  float r = pick_radius(p, center, radii);
  vec2 d = abs(p - center) - hs + r;
  return length(max(d, 0.0)) + min(max(d.x, d.y), 0.0) - r;
}

// Twin of Gpu.Sdf.squircleSdf — the .continuous corner style: the corner
// region measures the 4-norm, whose zero set is the superellipse
// |x|^4 + |y|^4 = r^4 (curvature-continuous edge joins); edges match
// rrect_sdf exactly.
float squircle_sdf(vec2 p, vec4 bounds, vec4 radii) {
  vec2 hs = bounds.zw * 0.5;
  vec2 center = bounds.xy + hs;
  float r = pick_radius(p, center, radii);
  vec2 d = abs(p - center) - hs + r;
  if (d.x > 0.0 && d.y > 0.0) {
    vec2 d2 = d * d;
    return sqrt(sqrt(dot(d2, d2))) - r;
  }
  return max(d.x, d.y) - r;
}
