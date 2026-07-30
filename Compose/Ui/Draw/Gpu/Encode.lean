module

public import Compose.Ui.Draw.DisplayList
public meta import Compose.Ui.Draw.DisplayList
public import Compose.Ui.Draw.Gpu.Instance
public meta import Compose.Ui.Draw.Gpu.Instance

public section

/-!
# GPU display-list encoder (`Compose/Ui/Draw/Gpu/Encode.lean`)

Pure lowering of a recorded `DisplayList` into the GPU pipelines' packed
buffers plus a flat `DrawCmd` list, replayed back-to-front by
`Gpu/Renderer.lean`. Text runs arrive pre-resolved (`ResolvedRun`, fetched in
IO by `Gpu/TextEngine.lean` in the same prim-walk order this encoder consumes
them).

Lowering per primitive:
- `rect`, and `shape` specs that are axis-aligned rounded geometry under a
  solid or two-stop gradient brush — linear, radial, or a sweep with exactly
  `(0, ·), (1, ·)` stops (`rrFill`/`rrStroke`, circles, axis-aligned lines) →
  **quad instances** (SDF coverage + per-fragment gradient `t` in the
  fragment shader, selected by `gradKind`).
- Everything else (`arcStroke`, angled lines, the ripple's
  `circleFillClipped`, multi-stop/off-spec-sweep or gradient-stroked
  brushes) → the **mesh pipeline**, reusing the exact CPU tessellation the
  SDL backend rasterizes.
- `text` → **glyph vertices** (atlas quads snapped once per run at the
  rounded run origin — the shimmer fix; SDL_ttf's y-up data maps as
  `screen = origin + (x, −y)`, probe-verified).
- `rrShadow` → **shadow instances** (the analytic Gaussian shader; blur `≤ 0`
  degrades to a hard offset fill quad, matching the tessellator).
- `image` → **textured quads on the layer pipeline** (image textures hold
  premultiplied pixels, exactly what its fragment samples; UVs cover the
  `src` fraction; the sampling mode picks the nearest or linear sampler at
  replay). Texture uploads happen before the encode (`Gpu.resolveImages`,
  walk-order indices like text).
- `layer` (alpha `< 1`, transformed, or carrying a blur effect) → an
  **offscreen layer pass**: the content encodes into its own command list
  with every coordinate shifted to the layer's origin (`LayerEnc`; packed
  buffers are shared across passes), and the parent list gets one `.layer`
  composite command. The content region is the recorded bounds (∩ clip when
  untransformed) plus a margin — 1 px AA, or a blur's `3σ + 1` spread —
  snapped to whole px so pixel-grid reasoning (text snapping) holds inside. A
  blur's σ rides the `LayerEnc` (the renderer inserts two separable Gaussian
  passes over the texture before it is composited). A
  composite transform is conjugated into the pass's coordinates and maps the
  composite quad's corners (`Affine.snapComposite` translations snap to the
  grid + nearest; others sample linearly); an enclosing clip scissors the
  composite. Identity props flatten inline. Layers are emitted
  innermost-first — the render order.
- `backdrop` → a **snapshot split** (`EncodeResult.snapshotSplit`): the first
  backdrop marks where the target list splits — the renderer replays the
  prefix into a full-screen snapshot, blurs each panel's region of it at a
  downsampled resolution (`BackdropEnc`), blits the snapshot 1:1, and the
  suffix's `.backdrop` commands composite the blurred panel quads (masked by
  the record-site rounded clip, like layer composites). A backdrop inside an
  *offscreen* layer's content is dropped (no scene behind it to snapshot —
  documented v1 constraint).

Clips: `PrimState.clip` becomes an integer scissor per command with the same
floor/ceil expansion as the SDL backend's clip rect, so the two backends clip
rectangularly identically. `PrimState.rounded` additionally becomes the
in-shader rounded mask on every quad-path primitive — exact rounded clipping
the SDL backend can only approximate (mesh/glyph/shadow content still gets
the rectangular scissor; the ripple's `circleFillClipped` uses its recorded
rrect as the mask, making the geometric clip exact too). Consecutive commands
with equal kind/scissor/atlas merge.
-/

namespace Compose.Draw.Gpu
open Compose.Draw

/-- One encoded offscreen layer: its composite region (integral, in the
coordinates of the pass that composites it — the target, or an enclosing
layer), the group alpha, and the commands rendered into its texture (their
coordinates and scissors are layer-local). -/
structure LayerEnc where
  /-- Content region (whole-px `Rect`, pre-transform — content renders
  axis-aligned into the texture at this region's size). -/
  bounds : Rect
  /-- Group alpha applied once at composite. -/
  alpha : Float32
  /-- Composite transform in the compositing pass's coordinates: the four
  corners of `bounds` map through it (`none` = axis-aligned at `bounds`).
  Near-integer pure translations arrive pre-snapped to the grid
  (`Affine.snapComposite`) so the composite stays pixel-exact. -/
  transform : Option Affine := none
  /-- Gaussian-blur standard deviation applied to the texture before the
  composite (`0` = none; `LayerEffect.blur`, normalized). The renderer runs
  two extra separable render passes; `bounds` already includes the `3σ + 1`
  spread margin. -/
  sigma : Float32 := 0
  /-- Signed per-axis overscroll-stretch intensity (`LayerEffect.stretch`,
  normalized): the composite draws through the stretch pipeline, which warps
  the UV before sampling — no extra pass, no spread. -/
  stretch : Option (Float32 × Float32) := none
  /-- The ambient rounded clip at the layer's record site, in the
  compositing pass's coordinates: the composite draw masks against it in the
  layer fragment (`LayerClip` uniform — exact rounded clipping of blurred/
  translucent composites; `none` pushes the unmasked huge-rect sentinel).
  Stretched composites ignore it (the stretch pipeline has its own fragment
  uniform; overscroll never records under a rounded clip in production). -/
  rounded : Option RoundRect := none
  /-- The layer's own render-pass commands. -/
  cmds : Array DrawCmd
  deriving Repr, BEq, Inhabited

/-- One encoded backdrop-frost panel (`Prim.backdrop`): the renderer splits
the target list at the first backdrop (`EncodeResult.snapshotSplit`),
replays the prefix into a full-screen snapshot texture, blurs this panel's
`region` of it at a downsampled resolution, and the `.backdrop` composite
command draws the `panel` quad sampling the blurred texture. All panels
share the one prefix snapshot — overlapping glass siblings don't frost each
other (the iOS-parity approximation, DESIGN.md). -/
structure BackdropEnc where
  /-- Blur-source region (whole-px, target coordinates): the panel inflated
  by the blur's full-res reach `3σ` plus the downsample halvings' bilinear
  bleed, so every visible panel texel blurs from real snapshot content. -/
  region : Rect
  /-- The visible panel quad (whole-px: recorded bounds ∩ clip, snapped
  outward) the composite draws. -/
  panel : Rect
  /-- Normalized blur σ in full-res device px (`0 < σ ≤ backdropSigmaMax`).
  The separable passes run at the downsampled resolution with `σ / 2^levels`. -/
  sigma : Float32
  /-- Downsample halvings before blurring (`1`, or `2` past σ 32 — keeps the
  effective σ ≤ 16, inside the blur pipeline's 48-tap reach). -/
  levels : Nat
  /-- The panel's rounded clip at the record site (target coordinates): the
  composite masks against it in the layer fragment (`LayerClip`); `none`
  composites unmasked. -/
  rounded : Option RoundRect := none
  /-- Normalized refractive edge bend (`Refraction`, device px): `strength`
  capped at 32, `band` floored at 1, `chroma` in `[0, 8]` — or all-off `{}`.
  When on, the composite runs the **glass** pipeline (SDF-gradient UV warp)
  instead of the plain layer composite, and `region` grows by
  `strength + chroma` so warped samples stay on real blurred content. -/
  refr : Refraction := {}
  deriving Repr, BEq, Inhabited

/-- A backdrop region extent downsampled by `k` halvings (whole px, ≥ 1) —
the renderer's texture-request and pass-extent arithmetic, shared with the
composite-quad UV math so they can never drift. -/
def backdropLevelDim (x : Float32) (k : Nat) : Float32 :=
  max 1 ((x / Float32.ofNat (2 ^ k)).ceil)

#guard backdropLevelDim 100 1 == 50
#guard backdropLevelDim 101 1 == 51
#guard backdropLevelDim 101 2 == 26   -- == ceil(ceil(101/2)/2): halvings compose
#guard backdropLevelDim 1 2 == 1

/-- Encoder output: one packed buffer per pipeline plus the replay commands.
`textsConsumed` is the number of text runs consumed (walk-order bookkeeping). -/
structure EncodeResult where
  /-- Packed `QuadInstance`s (`quadStride` bytes each). -/
  quads : ByteArray := .empty
  quadCount : Nat := 0
  /-- Packed `ShadowInstance`s (`shadowStride` bytes each). -/
  shadows : ByteArray := .empty
  shadowCount : Nat := 0
  /-- Packed mesh vertices (`meshVertexStride` bytes each). -/
  meshVerts : ByteArray := .empty
  meshVertCount : Nat := 0
  /-- Mesh triangle indices (u32 LE, absolute into `meshVerts`). -/
  meshIdx : ByteArray := .empty
  meshIdxCount : Nat := 0
  /-- Packed glyph vertices (`texVertexStride` bytes each). -/
  glyphVerts : ByteArray := .empty
  glyphVertCount : Nat := 0
  /-- Glyph triangle indices (u32 LE, absolute into `glyphVerts`). -/
  glyphIdx : ByteArray := .empty
  glyphIdxCount : Nat := 0
  /-- Packed image vertices (`texVertexStride` bytes each — the layer
  pipeline's layout). -/
  imageVerts : ByteArray := .empty
  imageVertCount : Nat := 0
  /-- Image triangle indices (u32 LE, absolute into `imageVerts`). -/
  imageIdx : ByteArray := .empty
  imageIdxCount : Nat := 0
  /-- Draws in paint order. -/
  cmds : Array DrawCmd := #[]
  /-- Offscreen layers, innermost-first (their render order; `DrawCmd.layer`
  indices point here). -/
  layers : Array LayerEnc := #[]
  /-- Backdrop-frost panels in paint order (`DrawCmd.backdrop` indices point
  here). -/
  backdrops : Array BackdropEnc := #[]
  /-- Where the target list splits for backdrop rendering: commands before
  this index replay into the full-screen snapshot pass, the rest (starting
  with the first `.backdrop`) replay into the target after a 1:1 blit of the
  snapshot. `none` = no backdrops — the target pass replays `cmds` whole. -/
  snapshotSplit : Option Nat := none
  /-- Text runs consumed so far. -/
  textsConsumed : Nat := 0
  /-- Image primitives consumed so far. -/
  imagesConsumed : Nat := 0

/-- Convert a float clip to an integer scissor, expanding to whole pixels
exactly like the SDL backend's clip rect (floor min corner, ceil max). -/
def scissorOf : Option Rect → Option Sdl.Rect
  | none => none
  | some r =>
    let l := r.left.floor.toInt32
    let t := r.top.floor.toInt32
    let rt := r.right.ceil.toInt32
    let bt := r.bottom.ceil.toInt32
    some ⟨l, t, max 0 (rt - l), max 0 (bt - t)⟩

#guard scissorOf (some ⟨0.4, 0.6, 10.2, 19.5⟩) == some ⟨0, 0, 11, 20⟩
#guard scissorOf none == none

/-- The scissor of a recorded clip inside a pass whose coordinates are the
record-time ones displaced by `shift` (zero for the main pass; a layer's
negated origin inside it). -/
private def scissorAt (clip : Option Rect) (shift : Offset) : Option Sdl.Rect :=
  scissorOf (clip.map (·.translate shift))

/-- Append a quad instance, extending the trailing `quads` command when the
scissor matches (instances are always contiguous). -/
private def pushQuad (st : EncodeResult) (q : QuadInstance)
    (scissor : Option Sdl.Rect) : EncodeResult :=
  let idx := st.quadCount
  let st := { st with quads := q.pack st.quads, quadCount := idx + 1 }
  match st.cmds.back? with
  | some (.quads first count s) =>
    if s == scissor then
      { st with cmds := st.cmds.set! (st.cmds.size - 1) (.quads first (count + 1) s) }
    else
      { st with cmds := st.cmds.push (.quads idx 1 scissor) }
  | _ => { st with cmds := st.cmds.push (.quads idx 1 scissor) }

/-- Append a shadow instance, extending the trailing `shadows` command when
the scissor matches. -/
private def pushShadow (st : EncodeResult) (sh : ShadowInstance)
    (scissor : Option Sdl.Rect) : EncodeResult :=
  let idx := st.shadowCount
  let st := { st with shadows := sh.pack st.shadows, shadowCount := idx + 1 }
  match st.cmds.back? with
  | some (.shadows first count s) =>
    if s == scissor then
      { st with cmds := st.cmds.set! (st.cmds.size - 1) (.shadows first (count + 1) s) }
    else
      { st with cmds := st.cmds.push (.shadows idx 1 scissor) }
  | _ => { st with cmds := st.cmds.push (.shadows idx 1 scissor) }

/-- Append a tessellated mesh (the SDL-parity fallback path), folding the
primitive's translation and alpha into the vertices exactly like
`SdlBackend.meshVertices`; indices are rebased to absolute so consecutive
meshes merge into one indexed draw. -/
private def pushMesh (st : EncodeResult) (m : Mesh) (origin : Offset)
    (alpha : Float32) (scissor : Option Sdl.Rect) : EncodeResult := Id.run do
  if m.isEmpty then return st
  let base := st.meshVertCount
  let first := st.meshIdxCount
  let mut verts := st.meshVerts
  for v in m.vertices do
    verts := packMeshVertex verts (v.pos + origin) (v.color.withAlpha (v.color.a * alpha))
  let mut idx := st.meshIdx
  for i in m.indices do
    idx := pushU32 idx (UInt32.ofNat (base + i.toNatClampNeg))
  let st := { st with
    meshVerts := verts
    meshVertCount := base + m.vertices.size
    meshIdx := idx
    meshIdxCount := first + m.indices.size }
  match st.cmds.back? with
  | some (.mesh f count s) =>
    if s == scissor then
      return { st with cmds := st.cmds.set! (st.cmds.size - 1) (.mesh f (count + m.indices.size) s) }
    else
      return { st with cmds := st.cmds.push (.mesh first m.indices.size scissor) }
  | _ => return { st with cmds := st.cmds.push (.mesh first m.indices.size scissor) }

/-- Append one resolved atlas sequence of a text run at the (already snapped)
`origin`, converting SDL_ttf's y-up coordinates. -/
private def pushGlyphSeq (color : Color) (alpha : Float32) (origin : Offset)
    (scissor : Option Sdl.Rect) (st : EncodeResult) (seq : ResolvedSeq) :
    EncodeResult := Id.run do
  let n := seq.xy.size / 2
  if n == 0 || seq.indices.isEmpty then return st
  -- `.color` (emoji) atlases carry the pixel colors; tint white per SDL's
  -- testgputext convention — but the run color's own alpha still folds in
  -- (the SDL backend sets `c.a * st.alpha * extraAlpha` as the text alpha,
  -- which SDL_ttf applies to color glyphs too). `.alpha` (and `.sdf`) tint
  -- with the run color.
  let a := color.a * alpha
  let vcolor := match seq.imageType with
    | .color => Color.white.withAlpha a
    | _ => color.withAlpha a
  let base := st.glyphVertCount
  let first := st.glyphIdxCount
  let mut verts := st.glyphVerts
  for j in [0:n] do
    let pos : Offset := ⟨origin.x + (seq.xy.get! (2*j)).toFloat32,
                         origin.y - (seq.xy.get! (2*j+1)).toFloat32⟩
    let uv : Offset := ⟨(seq.uv.get! (2*j)).toFloat32, (seq.uv.get! (2*j+1)).toFloat32⟩
    verts := packTexVertex verts pos uv vcolor
  let mut idx := st.glyphIdx
  for i in seq.indices do
    idx := pushU32 idx (UInt32.ofNat (base + i.toNatClampNeg))
  let st := { st with
    glyphVerts := verts
    glyphVertCount := base + n
    glyphIdx := idx
    glyphIdxCount := first + seq.indices.size }
  match st.cmds.back? with
  | some (.glyphs f count atlas s) =>
    if s == scissor && atlas == seq.atlas then
      let merged : DrawCmd := .glyphs f (count + seq.indices.size) atlas s
      return { st with cmds := st.cmds.set! (st.cmds.size - 1) merged }
    else
      return { st with cmds := st.cmds.push (.glyphs first seq.indices.size seq.atlas scissor) }
  | _ => return { st with cmds := st.cmds.push (.glyphs first seq.indices.size seq.atlas scissor) }

-- A `.color` (emoji) sequence tints white but still folds the run color's own
-- alpha with the folded prim alpha — `white.withAlpha (color.a * alpha)`, the
-- exact fold the SDL backend applies to color glyphs; `.alpha` sequences tint
-- with the full run color at the same alpha.
#guard
  let seq (t : Sdl.Ttf.ImageType) : ResolvedSeq :=
    { atlas := 0, xy := ⟨#[0, 0]⟩, uv := ⟨#[0, 0]⟩, indices := #[0, 0, 0], imageType := t }
  let run : Color := ⟨1, 0, 0, 0.5⟩          -- translucent run color
  let emoji := pushGlyphSeq run 0.5 .zero none {} (seq .color)
  let alpha := pushGlyphSeq run 0.5 .zero none {} (seq .alpha)
  emoji.glyphVerts == packTexVertex .empty .zero .zero (Color.white.withAlpha 0.25)
    && alpha.glyphVerts == packTexVertex .empty .zero .zero (run.withAlpha 0.25)

/-- Append one image draw: a textured quad at `dst` with UVs covering the
`src` fraction of the texture (the whole texture when `none`), the folded
alpha in the vertex color (the layer pipeline multiplies the premultiplied
sample by `color.a`). Extends the trailing `image` command when texture,
sampling, and scissor all match. -/
private def pushImage (st : EncodeResult) (texIdx : Nat) (img : ImageBitmap)
    (src : Option Rect) (dst : Rect) (linear : Bool) (alpha : Float32)
    (scissor : Option Sdl.Rect) : EncodeResult := Id.run do
  if dst.width <= 0 || dst.height <= 0 then return st
  let (u0, v0, u1, v1) := match src with
    | some s =>
      let iw := Float32.ofNat img.width
      let ih := Float32.ofNat img.height
      (s.left / iw, s.top / ih, s.right / iw, s.bottom / ih)
    | none => (0, 0, 1, 1)
  let c := Color.white.withAlpha alpha
  let base := st.imageVertCount
  let first := st.imageIdxCount
  let mut verts := st.imageVerts
  verts := packTexVertex verts ⟨dst.left, dst.top⟩ ⟨u0, v0⟩ c
  verts := packTexVertex verts ⟨dst.right, dst.top⟩ ⟨u1, v0⟩ c
  verts := packTexVertex verts ⟨dst.left, dst.bottom⟩ ⟨u0, v1⟩ c
  verts := packTexVertex verts ⟨dst.right, dst.bottom⟩ ⟨u1, v1⟩ c
  let mut idx := st.imageIdx
  for j in ([0, 1, 2, 1, 3, 2] : List Nat) do
    idx := pushU32 idx (UInt32.ofNat (base + j))
  let st := { st with
    imageVerts := verts, imageVertCount := base + 4
    imageIdx := idx, imageIdxCount := first + 6 }
  match st.cmds.back? with
  | some (.image f count tex lin s) =>
    if tex == texIdx && lin == linear && s == scissor then
      return { st with cmds := st.cmds.set! (st.cmds.size - 1) (.image f (count + 6) tex lin s) }
    else
      return { st with cmds := st.cmds.push (.image first 6 texIdx linear scissor) }
  | _ => return { st with cmds := st.cmds.push (.image first 6 texIdx linear scissor) }

/-! ## Shape lowering -/

/-- A brush lowered to the quad fill encoding: the two gradient endpoint
colors plus the `gradStart`/`gradDir`/`gradKind` parameters the fragment
evaluates (see `QuadInstance.gradKind`). `gradStart` is the only
position-valued field — `placeQuad` translates exactly it, which is correct
for every kind (linear start, radial center, sweep center; `gradDir` carries
direction/scale-bias/angle, all translation-invariant). -/
private structure QuadPaint where
  bg0 : Color
  bg1 : Color
  gradStart : Offset := .zero
  gradDir : Offset := .zero
  gradKind : Float32 := 0

/-- Copy a lowered brush's fill fields onto a quad instance. -/
private def QuadPaint.fill (p : QuadPaint) (q : QuadInstance) : QuadInstance :=
  { q with bg0 := p.bg0, bg1 := p.bg1, gradStart := p.gradStart
           gradDir := p.gradDir, gradKind := p.gradKind }

/-- Lower a brush to the quad fill encoding. Solid → equal endpoints, zero
projection. Linear 2-stop → `t = saturate(dot(p − start, dir))` with `dir`
scaled by `1/len²` and the stop fractions folded into `start`/`dir`. Radial
2-stop → center + `(scale, bias)` with the stop remap folded in
(`t = saturate(|p − c|·scale + bias)`, twin `Gpu.Sdf.radialT`). Sweep with
exactly `(0, ·), (1, ·)` stops → center + `(startAngle, ·)` (the wrapped
fraction can't fold a stop remap — off-spec sweeps tessellate). `none` = the
brush needs the mesh path. Coordinates stay local; the caller translates by
the primitive origin. -/
private def quadBrush : Brush → Option QuadPaint
  | .solid c => some { bg0 := c, bg1 := c }
  | .linearGradient stops start stop => do
    unless stops.size == 2 do failure
    let (f0, c0) := stops[0]!
    let (f1, c1) := stops[1]!
    unless f1 - f0 > 1e-6 do failure
    let axis := stop - start
    let s := start + axis * f0
    let d := axis * (f1 - f0)
    let len2 := Offset.dot d d
    unless len2 > 1e-9 do failure
    some { bg0 := c0, bg1 := c1, gradStart := s, gradDir := ⟨d.x / len2, d.y / len2⟩ }
  | .radialGradient stops center radius => do
    unless stops.size == 2 do failure
    let (f0, c0) := stops[0]!
    let (f1, c1) := stops[1]!
    let span := f1 - f0
    unless span > 1e-6 do failure
    unless radius > 1e-6 do failure
    some { bg0 := c0, bg1 := c1, gradStart := center
           gradDir := ⟨1 / (radius * span), -(f0 / span)⟩, gradKind := 1 }
  | .sweepGradient stops center startAngle => do
    unless stops.size == 2 do failure
    let (f0, c0) := stops[0]!
    let (f1, c1) := stops[1]!
    unless f0 == 0 && f1 == 1 do failure
    some { bg0 := c0, bg1 := c1, gradStart := center
           gradDir := ⟨startAngle, 0⟩, gradKind := 2 }

/-- The quad geometry of a normalized rounded rect: origin, size, per-corner
circular radii (elliptical corners degrade to the x radius — no production
producer emits them). -/
private def rrQuad (rr : RoundRect) : Offset × Size × (Float32 × Float32 × Float32 × Float32) :=
  let rr := rr.normalize
  (⟨rr.rect.left, rr.rect.top⟩, ⟨rr.rect.width, rr.rect.height⟩,
   (rr.topLeft.x, rr.topRight.x, rr.bottomRight.x, rr.bottomLeft.x))

/-- Lower a shape spec to a quad instance in local coordinates, or `none` for
the mesh-tessellation path (arcs, angled lines, the clipped ripple, non-quad
brushes; strokes take only solid brushes — a gradient stroke tessellates). -/
private def lowerShape : ShapeSpec → Option QuadInstance
  | .rrFill rr brush => do
    let p ← quadBrush brush
    let (o, sz, (tl, tr, br, bl)) := rrQuad rr
    some (p.fill { origin := o, size := sz, radiusTL := tl, radiusTR := tr
                   radiusBR := br, radiusBL := bl })
  | .rrStroke rr width brush =>
    match brush with
    | .solid c =>
      let (o, sz, (tl, tr, br, bl)) := rrQuad rr
      some { origin := o, size := sz, radiusTL := tl, radiusTR := tr
             radiusBR := br, radiusBL := bl, borderColor := c, borderWidth := width }
    | _ => none
  | .circleFill center radius brush => do
    let p ← quadBrush brush
    some (p.fill { origin := ⟨center.x - radius, center.y - radius⟩
                   size := ⟨radius * 2, radius * 2⟩
                   radiusTL := radius, radiusTR := radius
                   radiusBR := radius, radiusBL := radius })
  | .circleStroke center radius width brush =>
    match brush with
    | .solid c =>
      some { origin := ⟨center.x - radius, center.y - radius⟩
             size := ⟨radius * 2, radius * 2⟩
             radiusTL := radius, radiusTR := radius, radiusBR := radius, radiusBL := radius
             borderColor := c, borderWidth := width }
    | _ => none
  | .line p0 p1 width brush =>
    match brush with
    | .solid c =>
      if p0.y == p1.y && width > 0 then       -- horizontal, butt caps
        some { origin := ⟨min p0.x p1.x, p0.y - width / 2⟩
               size := ⟨(p1.x - p0.x).abs, width⟩, bg0 := c, bg1 := c }
      else if p0.x == p1.x && width > 0 then  -- vertical
        some { origin := ⟨p0.x - width / 2, min p0.y p1.y⟩
               size := ⟨width, (p1.y - p0.y).abs⟩, bg0 := c, bg1 := c }
      else none
    | _ => none
  -- Paths always tessellate: the band-sweep mesh (fills, clipped fills, and
  -- stroke outlines alike) IS the path rasterization on both backends (a
  -- stencil-cover GPU path is noted future work, DESIGN.md).
  | .pathFill .. | .pathFillClipped .. | .pathStroke .. => none
  -- Handled by dedicated `encodePrim` arms (never reaches `lowerShape`).
  | .circleFillClipped .. | .arcStroke .. | .rrShadow .. => none

/-- Translate a local-coordinate quad to target px and fold the primitive
alpha into its colors. -/
private def placeQuad (q : QuadInstance) (origin : Offset) (alpha : Float32) :
    QuadInstance :=
  { q with
    origin := q.origin + origin
    gradStart := q.gradStart + origin
    bg0 := q.bg0.withAlpha (q.bg0.a * alpha)
    bg1 := q.bg1.withAlpha (q.bg1.a * alpha)
    borderColor := q.borderColor.withAlpha (q.borderColor.a * alpha) }

/-- Set a quad's in-shader rounded clip mask from a rounded rect already in
the pass's final coordinates (elliptical corners degrade to the x radius,
like the shape itself). -/
private def maskQuadRR (q : QuadInstance) (rr : RoundRect) : QuadInstance :=
  let rr := rr.normalize
  { q with
    clipOrigin := ⟨rr.rect.left, rr.rect.top⟩
    clipSize := ⟨rr.rect.width, rr.rect.height⟩
    clipRadiusTL := rr.topLeft.x, clipRadiusTR := rr.topRight.x
    clipRadiusBR := rr.bottomRight.x, clipRadiusBL := rr.bottomLeft.x }

/-- Apply the primitive's ambient rounded clip (recorded in render-target
coordinates) as the quad's mask; `none` leaves the huge default (unmasked). -/
private def maskQuad (q : QuadInstance) (rounded : Option RoundRect)
    (shift : Offset) : QuadInstance :=
  match rounded with
  | none => q
  | some rr => maskQuadRR q (rr.translate shift)

/-! ## The walk -/

/-- Encode one primitive. `shift` displaces record-time coordinates into the
current pass's (zero for the main pass; a layer's negated snapped origin
inside its content); `extraAlpha` is the folded alpha of enclosing
`alpha ≥ 1` layers; `inLayer` marks encoding inside an *offscreen* layer's
command list (where a backdrop has no scene behind it to snapshot — it is
dropped there; inline-flattened layers stay in the target pass and keep it). -/
private partial def encodePrim (texts : Array ResolvedRun) (images : Array Nat)
    (extraAlpha : Float32) (shift : Offset) (inLayer : Bool) (st : EncodeResult) :
    Prim → EncodeResult
  | .rect s color topLeft size =>
    if size.isEmpty then st
    else
      let alpha := s.alpha * extraAlpha
      let c := color.withAlpha (color.a * alpha)
      pushQuad st
        (maskQuad { origin := s.origin + shift + topLeft, size, bg0 := c, bg1 := c }
          s.rounded shift)
        (scissorAt s.clip shift)
  | .shape s spec cached =>
    let alpha := s.alpha * extraAlpha
    let origin := s.origin + shift
    let scissor := scissorAt s.clip shift
    match spec with
    | .rrShadow rr off blur color =>
      if color.a * alpha <= 0 then st
      else if blur <= 0 then
        -- Degenerate hard shadow: a plain offset fill (the tessellator's
        -- degenerate case), still under the ambient rounded mask.
        let (o, sz, (tl, tr, br, bl)) := rrQuad (rr.translate off)
        pushQuad st
          (maskQuad (placeQuad
            { origin := o, size := sz, radiusTL := tl, radiusTR := tr
              radiusBR := br, radiusBL := bl, bg0 := color, bg1 := color }
            origin alpha) s.rounded shift)
          scissor
      else
        let rrn := (rr.translate (origin + off)).normalize
        -- No in-shader mask on shadows (scissor only) — a shadow under a
        -- rounded clip is not a production shape.
        pushShadow st
          { origin := ⟨rrn.rect.left, rrn.rect.top⟩
            size := ⟨rrn.rect.width, rrn.rect.height⟩
            color := color.withAlpha (color.a * alpha)
            sigma := max 0.5 (blur / 2)
            corner := rrn.topLeft.x }
          scissor
    | .circleFillClipped center radius rr brush =>
      -- The bounded ripple: on the GPU the recorded rrect (local coordinates,
      -- like `center`) becomes the exact in-shader mask of a circle quad —
      -- no Sutherland–Hodgman mesh needed.
      match quadBrush brush with
      | some p =>
        let q : QuadInstance := p.fill
          { origin := ⟨center.x - radius, center.y - radius⟩
            size := ⟨radius * 2, radius * 2⟩
            radiusTL := radius, radiusTR := radius
            radiusBR := radius, radiusBL := radius }
        pushQuad st (maskQuadRR (placeQuad q origin alpha) (rr.translate origin)) scissor
      | none => pushMesh st ((cached.map (·.mesh)).getD spec.tessellate) origin alpha scissor
    | _ =>
      match lowerShape spec with
      | some q => pushQuad st (maskQuad (placeQuad q origin alpha) s.rounded shift) scissor
      | none => pushMesh st ((cached.map (·.mesh)).getD spec.tessellate) origin alpha scissor
  | .mesh s m => pushMesh st m (s.origin + shift) (s.alpha * extraAlpha) (scissorAt s.clip shift)
  | .text s run =>
    let runIdx := st.textsConsumed
    let st := { st with textsConsumed := runIdx + 1 }
    match texts[runIdx]? with
    | none => st
    | some seqs =>
      -- Snap once per run in device px (the shimmer fix, shared with the
      -- SDL backend): intra-run subpixel layout is preserved, the run origin
      -- lands on the pixel grid (`shift` is integral, so snapping commutes
      -- with the layer displacement).
      let origin := snapTextOrigin s.origin shift
      seqs.foldl (pushGlyphSeq run.color (s.alpha * extraAlpha) origin (scissorAt s.clip shift)) st
  | .image s img src dst sampling =>
    let imgIdx := st.imagesConsumed
    let st := { st with imagesConsumed := imgIdx + 1 }
    match images[imgIdx]? with
    | none => st
    | some texIdx =>
      pushImage st texIdx img src (dst.translate (s.origin + shift))
        (sampling == .linear) (s.alpha * extraAlpha) (scissorAt s.clip shift)
  | .backdrop s bounds sigma refr =>
    -- Inside an offscreen layer's pass there is no "scene behind" to
    -- snapshot: drop the panel (documented v1 constraint — glass under an
    -- alpha/blur/transform layer keeps its tint without frost).
    if inLayer then st else Id.run do
    let sigma := min sigma backdropSigmaMax
    if sigma <= 0 then return st
    -- Normalize the refraction: off unless strength > 0; strength/chroma
    -- capped so the region margin stays bounded, band floored at 1 (the
    -- falloff divides by it).
    let refr : Refraction :=
      if refr.strength > 0 then
        { strength := min refr.strength 32, band := max refr.band 1
          chroma := min (max refr.chroma 0) 8 }
      else {}
    -- The visible panel: recorded bounds ∩ clip, snapped outward to whole px.
    let p := bounds.translate (s.origin + shift)
    let p := match s.clip with | some c => Rect.intersect p c | none => p
    let panel : Rect := ⟨p.left.floor, p.top.floor, p.right.ceil, p.bottom.ceil⟩
    if panel.width < 1 || panel.height < 1 then return st
    -- Blur-source region: the taps' full-res reach (3σ) plus the downsample
    -- halvings' bilinear bleed (≤ 4 px at two levels), plus the refraction's
    -- outward sampling reach when the bend is on.
    let m := 3 * sigma + 4 + refr.strength + refr.chroma
    let region : Rect := ⟨(panel.left - m).floor, (panel.top - m).floor,
                          (panel.right + m).ceil, (panel.bottom + m).ceil⟩
    let idx := st.backdrops.size
    return { st with
      snapshotSplit := some (st.snapshotSplit.getD st.cmds.size)
      cmds := st.cmds.push (.backdrop idx (scissorAt s.clip shift))
      backdrops := st.backdrops.push
        { region, panel, sigma
          levels := if sigma > 32 then 2 else 1
          rounded := s.rounded.map (·.translate shift)
          refr } }
  | .layer s bounds props content =>
    let effect := props.effect.normalize
    if props.transform.isNone && props.alpha ≥ 1.0 && effect == .none then
      -- No compositing needed: flatten inline (records don't produce these;
      -- hand-built lists may). `inLayer` passes through — flattened content
      -- draws in the enclosing pass, so a backdrop here keeps its meaning.
      content.foldl (encodePrim texts images (extraAlpha * props.alpha) shift inLayer) st
    else Id.run do
      -- Conjugate the record-time transform into this pass's coordinates
      -- (`shift` is integral): pass = record + shift ⟹ T(shift)∘t∘T(−shift).
      -- Near-integer pure translations snap to the grid and composite
      -- nearest (crisp, parity-stable); everything else filters linearly.
      let (transform, linear) := match props.transform with
        | none => (none, false)
        | some t =>
          let t := (Affine.translation shift).comp (t.comp (Affine.translation (-shift)))
          if t.snapComposite then
            (some (Affine.translation ⟨t.tx.round, t.ty.round⟩), false)
          else
            (some t, true)
      -- Content region: bounds plus a margin — 1 px AA, or a blur's `3σ + 1`
      -- spread (the tails must render and composite) — snapped to whole px
      -- (kept ≥ 1×1 even when degenerate so the text-run walk stays aligned
      -- with `resolveTexts`). An enclosing clip crops untransformed content
      -- directly; under a transform it scissors the *composite* instead
      -- (target-coordinate clips apply to where pixels land).
      let m := max 1 effect.spread
      let r := match s.clip, transform with
        | some c, none => Rect.intersect bounds c
        | _, _ => bounds
      let l := (r.left + shift.x - m).floor
      let t := (r.top + shift.y - m).floor
      let rt := max ((r.right + shift.x + m).ceil) (l + 1)
      let bt := max ((r.bottom + shift.y + m).ceil) (t + 1)
      let saved := st.cmds
      -- Content encodes at ambient alpha 1: the enclosing flattened alpha
      -- applies exactly once, at the composite below (SDL-backend parity —
      -- its offscreen path renders content with `extraAlpha` 1.0 too).
      let st := content.foldl (encodePrim texts images 1.0 (shift - ⟨l, t⟩) true)
        { st with cmds := #[] }
      let idx := st.layers.size
      return { st with
        cmds := saved.push (.layer idx linear (scissorAt s.clip shift))
        layers := st.layers.push
          { bounds := ⟨l, t, rt, bt⟩, alpha := props.alpha * extraAlpha
            transform, sigma := match effect with | .blur sg => sg | _ => 0
            stretch := match effect with | .stretch sx sy => some (sx, sy) | _ => none
            rounded := s.rounded.map (·.translate shift)
            cmds := st.cmds } }

/-- Encode a display list against its resolved text runs and image texture
indices (both in the same prim-walk order `Gpu.resolveTexts` /
`Gpu.resolveImages` produced them). -/
def encode (list : DisplayList) (texts : Array ResolvedRun)
    (images : Array Nat := #[]) : EncodeResult :=
  list.foldl (encodePrim texts images 1.0 .zero false) {}

-- One crisp rect → one quad instance, one command, no tessellation output.
#guard
  let r := encode #[.rect {} .red ⟨2, 3⟩ ⟨10, 20⟩] #[]
  r.quadCount == 1 && r.quads.size == quadStride
    && r.cmds == #[.quads 0 1 none] && r.meshIdxCount == 0
-- Adjacent rects with the same clip merge into one command.
#guard
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨1, 1⟩, .rect {} .blue ⟨2, 0⟩ ⟨1, 1⟩] #[]
  r.quadCount == 2 && r.cmds == #[.quads 0 2 none]
-- A clip change splits commands and produces the SDL-expanded scissor.
#guard
  let st : PrimState := { clip := some ⟨0, 0, 10.5, 10⟩ }
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨1, 1⟩, .rect st .blue ⟨0, 0⟩ ⟨1, 1⟩] #[]
  r.cmds == #[.quads 0 1 none, .quads 1 1 (some ⟨0, 0, 11, 10⟩)]
-- Solid rounded fills and strokes lower to quads; arcs fall back to the mesh
-- pipeline; interleaving splits commands at each kind switch.
#guard
  let rr := RoundRect.circular ⟨0, 0, 40, 40⟩ 8
  let r := encode
    #[.shape {} (.rrFill rr (.solid .red)) none,
      .shape {} (.arcStroke ⟨50, 50⟩ 20 0 3 4 (.solid .blue)) none,
      .shape {} (.rrStroke rr 2 (.solid .black)) none] #[]
  r.quadCount == 2 && r.cmds.size == 3
    && r.meshIdxCount > 0 && r.meshVerts.size == r.meshVertCount * meshVertexStride
-- A two-stop gradient fill stays on the quad path; three stops tessellate.
#guard
  let rr := RoundRect.circular ⟨0, 0, 40, 40⟩ 8
  let g2 : Brush := .gradient .black .white ⟨0, 0⟩ ⟨40, 0⟩
  let g3 : Brush := .linearGradient #[(0, Color.red), (0.5, .green), (1, .blue)] ⟨0, 0⟩ ⟨40, 0⟩
  let r := encode #[.shape {} (.rrFill rr g2) none, .shape {} (.rrFill rr g3) none] #[]
  r.quadCount == 1 && r.meshIdxCount > 0
-- A 2-stop radial fill lowers to a quad with `gradKind` 1 and the stop remap
-- folded into (scale, bias): stops (0.25, 0.75) on radius 10 give scale
-- 1/(10·0.5) = 0.2, bias −0.25/0.5 = −0.5. The primitive origin translates
-- only the center (`placeQuad`), never the scale/bias.
#guard
  let b : Brush := .radialGradient #[(0.25, Color.red), (0.75, .blue)] ⟨20, 20⟩ 10
  let r := encode
    #[.shape { origin := ⟨5, 5⟩ } (.rrFill (RoundRect.ofRect ⟨0, 0, 40, 40⟩) b) none] #[]
  let want : QuadInstance :=
    { origin := ⟨5, 5⟩, size := ⟨40, 40⟩, bg0 := .red, bg1 := .blue
      gradStart := ⟨25, 25⟩, gradDir := ⟨0.2, -0.5⟩, gradKind := 1 }
  r.quadCount == 1 && r.meshIdxCount == 0 && r.quads == want.pack .empty
-- An on-spec sweep lowers to `gradKind` 2 carrying (startAngle, ·); a
-- fraction-shifted sweep and a 3-stop radial take the mesh path.
#guard
  let rect := RoundRect.ofRect ⟨0, 0, 40, 40⟩
  let enc (b : Brush) := encode #[.shape {} (.rrFill rect b) none] #[]
  let ok := enc (.sweepGradient #[(0, Color.red), (1, .blue)] ⟨20, 20⟩ 1)
  let want : QuadInstance :=
    { origin := ⟨0, 0⟩, size := ⟨40, 40⟩, bg0 := .red, bg1 := .blue
      gradStart := ⟨20, 20⟩, gradDir := ⟨1, 0⟩, gradKind := 2 }
  ok.quadCount == 1 && ok.quads == want.pack .empty
    && (enc (.sweepGradient #[(0.1, Color.red), (1, .blue)] ⟨20, 20⟩)).quadCount == 0
    && (enc (.sweepGradient #[(0.1, Color.red), (1, .blue)] ⟨20, 20⟩)).meshIdxCount > 0
    && (enc (.radialGradient #[(0, Color.red), (0.5, .green), (1, .blue)] ⟨20, 20⟩ 10)).quadCount == 0
-- A full-alpha untransformed layer flattens inline (no offscreen pass).
#guard
  let inner : Prim := .rect {} .red ⟨0, 0⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨0, 0, 4, 4⟩ {} #[inner]] #[]
  r.quadCount == 1 && r.cmds == #[.quads 0 1 none] && r.layers.isEmpty
-- A translucent layer becomes an offscreen pass: bounds get the 1 px AA
-- margin and whole-px snap, content coordinates shift to the layer origin,
-- and the parent list holds one composite command.
#guard
  let inner : Prim := .rect {} .red ⟨10, 10⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩ { alpha := 0.5 } #[inner]] #[]
  r.layers.size == 1 && r.cmds == #[.layer 0 false none]
    && r.layers[0]!.bounds == (⟨7, 7, 25, 25⟩ : Rect) && r.layers[0]!.alpha == 0.5
    && r.layers[0]!.transform == none
    && r.layers[0]!.cmds == #[.quads 0 1 none]
    && r.quads == (encode #[.rect {} .red ⟨3, 3⟩ ⟨4, 4⟩] #[]).quads
-- Ambient flattened alpha reaching an offscreen layer applies exactly once,
-- at the composite: the content encodes at full alpha (SDL-backend parity;
-- ambient alpha ≠ 1 needs a hand-built `alpha > 1` flatten layer today).
#guard
  let inner : Prim := .layer {} ⟨0, 0, 4, 4⟩ { alpha := 0.5 } #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]
  let r := encode #[.layer {} ⟨0, 0, 8, 8⟩ { alpha := 2.0 } #[inner]] #[]
  -- The outer `alpha ≥ 1` layer flattens inline (extraAlpha 2); the inner
  -- layer goes offscreen with composite alpha 0.5 × 2 = 1 and content
  -- vertices identical to an unlayered encode (shifted by the 1 px margin).
  r.layers.size == 1 && r.layers[0]!.alpha == 1.0
    && r.layers[0]!.cmds == #[.quads 0 1 none]
    && r.quads == (encode #[.rect {} .red ⟨1, 1⟩ ⟨4, 4⟩] #[]).quads
-- Nested layers emit innermost-first; the outer layer composites the inner.
#guard
  let inner : Prim := .layer {} ⟨0, 0, 4, 4⟩ { alpha := 0.5 } #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]
  let r := encode #[.layer {} ⟨0, 0, 8, 8⟩ { alpha := 0.25 } #[inner]] #[]
  r.layers.size == 2 && r.cmds == #[.layer 1 false none]
    && r.layers[1]!.cmds == #[.layer 0 false none] && r.layers[0]!.alpha == 0.5
-- A transformed layer records a pass even at alpha 1: the transform rides
-- the LayerEnc, the composite samples linearly, and the enclosing clip does
-- NOT crop the content region (it scissors the composite instead).
#guard
  let t := Affine.rotation 0.5
  let st : PrimState := { clip := some ⟨0, 0, 10, 10⟩ }
  let r := encode #[.layer st ⟨8, 8, 24, 24⟩ { transform := some t }
    #[.rect {} .red ⟨10, 10⟩ ⟨4, 4⟩]] #[]
  r.layers.size == 1 && r.cmds == #[.layer 0 true (some ⟨0, 0, 10, 10⟩)]
    && r.layers[0]!.bounds == (⟨7, 7, 25, 25⟩ : Rect)
    && r.layers[0]!.transform == some t && r.layers[0]!.alpha == 1
-- A blur forces an offscreen pass even at alpha 1, carries its σ, and the
-- content region grows by the 3σ + 1 spread (σ = 2 ⟹ margin 7); the content
-- shifts by the inflated origin.
#guard
  let inner : Prim := .rect {} .red ⟨10, 10⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩ { effect := .blur 2 } #[inner]] #[]
  r.layers.size == 1 && r.cmds == #[.layer 0 false none]
    && r.layers[0]!.bounds == (⟨1, 1, 31, 31⟩ : Rect) && r.layers[0]!.sigma == 2
    && r.layers[0]!.alpha == 1
    && r.quads == (encode #[.rect {} .red ⟨9, 9⟩ ⟨4, 4⟩] #[]).quads
-- A degenerate blur (σ ≤ 0) normalizes away — the layer flattens inline; an
-- oversized σ caps at 16.
#guard
  let inner : Prim := .rect {} .red ⟨0, 0⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨0, 0, 4, 4⟩ { effect := .blur 0 } #[inner]] #[]
  let big := encode #[.layer {} ⟨0, 0, 4, 4⟩ { effect := .blur 99 } #[inner]] #[]
  r.layers.isEmpty && r.cmds == #[.quads 0 1 none]
    && big.layers[0]!.sigma == 16
-- A stretch forces an offscreen composite even at alpha 1, carries its
-- intensity, spreads nothing (margin stays the 1 px AA), and never blurs.
#guard
  let inner : Prim := .rect {} .red ⟨10, 10⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩ { effect := .stretch 0 0.03 } #[inner]] #[]
  r.layers.size == 1 && r.cmds == #[.layer 0 false none]
    && r.layers[0]!.bounds == (⟨7, 7, 25, 25⟩ : Rect)
    && r.layers[0]!.stretch == some (0, 0.03) && r.layers[0]!.sigma == 0
-- A near-integer pure translation snaps to the grid and composites nearest.
#guard
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩
    { transform := some (.translation ⟨3.004, -2⟩) } #[.rect {} .red ⟨10, 10⟩ ⟨4, 4⟩]] #[]
  r.cmds == #[.layer 0 false none]
    && r.layers[0]!.transform == some (.translation ⟨3, -2⟩)
-- Inside an enclosing layer pass the transform is conjugated by the pass
-- shift: a 2× scale about (0,0) in record coordinates keeps (0,0) fixed, so
-- in the inner pass (shifted by −(−1,−1) = +1) the fixed point is (1,1).
#guard
  let inner : Prim := .layer {} ⟨0, 0, 4, 4⟩
    { transform := some (.scaling 2 2) } #[.rect {} .red ⟨0, 0⟩ ⟨2, 2⟩]
  let r := encode #[.layer {} ⟨0, 0, 8, 8⟩ { alpha := 0.5 } #[inner]] #[]
  r.layers.size == 2
    && (r.layers[0]!.transform.getD .identity).mapOffset ⟨1, 1⟩ == ⟨1, 1⟩
    && (r.layers[0]!.transform.getD .identity).mapOffset ⟨2, 1⟩ == ⟨3, 1⟩
-- A rounded clip enclosing an offscreen layer rides the LayerEnc (the
-- composite's in-shader mask); an unclipped layer records `none`.
#guard
  let rr := RoundRect.circular ⟨0, 0, 40, 40⟩ 8
  let st : PrimState := { clip := some ⟨0, 0, 40, 40⟩, rounded := some rr }
  let r := encode #[.layer st ⟨0, 0, 40, 40⟩ { alpha := 0.5 }
    #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]] #[]
  r.layers.size == 1 && r.layers[0]!.rounded == some rr
    && (encode #[.layer {} ⟨0, 0, 40, 40⟩ { alpha := 0.5 }
          #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]] #[]).layers[0]!.rounded == none
-- Inside an enclosing layer pass the rounded mask shifts into that pass's
-- coordinates (outer bounds ⟨0,0,8,8⟩ inflate to origin (−1,−1), so the
-- inner mask translates by +1).
#guard
  let rr := RoundRect.circular ⟨0, 0, 4, 4⟩ 2
  let inner : Prim := .layer { rounded := some rr } ⟨0, 0, 4, 4⟩ { alpha := 0.5 }
    #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]
  let r := encode #[.layer {} ⟨0, 0, 8, 8⟩ { alpha := 0.5 } #[inner]] #[]
  r.layers.size == 2 && r.layers[0]!.rounded == some (rr.translate ⟨1, 1⟩)
-- The ambient rounded clip becomes the quad's in-shader mask.
#guard
  let rr := RoundRect.circular ⟨0, 0, 40, 40⟩ 8
  let st : PrimState := { clip := some ⟨0, 0, 40, 40⟩, rounded := some rr }
  let r := encode #[.rect st .red ⟨0, 0⟩ ⟨40, 40⟩] #[]
  let want : QuadInstance :=
    { origin := ⟨0, 0⟩, size := ⟨40, 40⟩, bg0 := .red, bg1 := .red
      clipOrigin := ⟨0, 0⟩, clipSize := ⟨40, 40⟩
      clipRadiusTL := 8, clipRadiusTR := 8, clipRadiusBR := 8, clipRadiusBL := 8 }
  r.quads == want.pack .empty && r.cmds == #[.quads 0 1 (some ⟨0, 0, 40, 40⟩)]
-- The bounded ripple lowers to a masked circle quad — no mesh.
#guard
  let rr := RoundRect.circular ⟨0, 0, 40, 40⟩ 8
  let r := encode #[.shape { origin := ⟨5, 5⟩ }
    (.circleFillClipped ⟨20, 20⟩ 10 rr (.solid .red)) none] #[]
  let want : QuadInstance :=
    { origin := ⟨15, 15⟩, size := ⟨20, 20⟩
      radiusTL := 10, radiusTR := 10, radiusBR := 10, radiusBL := 10
      bg0 := .red, bg1 := .red, gradStart := ⟨5, 5⟩
      clipOrigin := ⟨5, 5⟩, clipSize := ⟨40, 40⟩
      clipRadiusTL := 8, clipRadiusTR := 8, clipRadiusBR := 8, clipRadiusBL := 8 }
  r.quadCount == 1 && r.meshIdxCount == 0 && r.quads == want.pack .empty
-- Shadows encode as analytic instances (offset applied, σ = blur/2) and
-- consecutive ones merge; blur 0 degrades to a hard offset-fill quad.
#guard
  let sh : Prim := .shape {}
    (.rrShadow (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) ⟨0, 2⟩ 4 (Color.black.withAlpha 0.25)) none
  let r := encode #[sh, sh] #[]
  let want : ShadowInstance :=
    { origin := ⟨0, 2⟩, size := ⟨40, 40⟩, color := Color.black.withAlpha 0.25
      sigma := 2, corner := 8 }
  r.shadowCount == 2 && r.cmds == #[.shadows 0 2 none]
    && r.shadows == want.pack (want.pack .empty)
#guard
  let r := encode #[.shape {}
    (.rrShadow (RoundRect.ofRect ⟨0, 0, 10, 10⟩) ⟨0, 2⟩ 0 .black) none] #[]
  r.shadowCount == 0 && r.quadCount == 1
-- Consecutive meshes merge into one indexed draw with absolute indices.
#guard
  let arc : Prim := .shape {} (.arcStroke ⟨50, 50⟩ 20 0 3 4 (.solid .blue)) none
  let r := encode #[arc, arc] #[]
  r.cmds.size == 1 && (match r.cmds[0]! with | .mesh 0 n none => n == r.meshIdxCount | _ => false)
-- A backdrop splits the target list at its command index: the prefix (the
-- content behind it) goes to the snapshot pass, the panel snaps outward to
-- whole px, and the region adds the 3σ + 4 reach. σ ≤ 32 → one halving.
#guard
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨100, 100⟩,
                    .backdrop {} ⟨10.4, 10.6, 50, 50⟩ 8,
                    .rect {} .blue ⟨0, 0⟩ ⟨4, 4⟩] #[]
  r.snapshotSplit == some 1 && r.cmds == #[.quads 0 1 none, .backdrop 0 none, .quads 1 1 none]
    && r.backdrops.size == 1
    && r.backdrops[0]!.panel == (⟨10, 10, 50, 50⟩ : Rect)
    && r.backdrops[0]!.region == (⟨-18, -18, 78, 78⟩ : Rect)
    && r.backdrops[0]!.sigma == 8 && r.backdrops[0]!.levels == 1
    && r.backdrops[0]!.rounded == none
-- The record-site rounded clip rides the BackdropEnc (the composite mask),
-- and the clip both scissors the command and crops the panel.
#guard
  let rr := RoundRect.circular ⟨10, 10, 40, 40⟩ 12
  let st : PrimState := { clip := some ⟨10, 10, 40, 40⟩, rounded := some rr }
  let r := encode #[.backdrop st ⟨0, 0, 60, 60⟩ 8] #[]
  r.snapshotSplit == some 0 && r.cmds == #[.backdrop 0 (some ⟨10, 10, 30, 30⟩)]
    && r.backdrops[0]!.panel == (⟨10, 10, 40, 40⟩ : Rect)
    && r.backdrops[0]!.rounded == some rr
-- σ caps at backdropSigmaMax and > 32 takes the second halving; σ ≤ 0 and
-- fully-clipped panels drop (no split, no command).
#guard
  let r := encode #[.backdrop {} ⟨0, 0, 50, 50⟩ 99] #[]
  r.backdrops[0]!.sigma == 64 && r.backdrops[0]!.levels == 2
-- Refraction rides the BackdropEnc normalized (strength ≤ 32, band ≥ 1,
-- chroma ∈ [0, 8]) and grows the region margin by strength + chroma; a
-- zero-strength spec normalizes to all-off `{}` and leaves the margin alone.
#guard
  let r := encode #[.backdrop {} ⟨0, 0, 50, 50⟩ 8 { strength := 10, band := 20 }] #[]
  r.backdrops[0]!.refr == { strength := 10, band := 20 }
    && r.backdrops[0]!.region == (⟨-38, -38, 88, 88⟩ : Rect)   -- 3·8 + 4 + 10
#guard
  let r := encode #[.backdrop {} ⟨0, 0, 50, 50⟩ 8
    { strength := 99, band := 0, chroma := 99 }] #[]
  r.backdrops[0]!.refr == { strength := 32, band := 1, chroma := 8 }
#guard
  let r := encode #[.backdrop {} ⟨0, 0, 50, 50⟩ 8 { strength := 0, chroma := 5 }] #[]
  r.backdrops[0]!.refr == ({} : Refraction)
    && r.backdrops[0]!.region == (⟨-28, -28, 78, 78⟩ : Rect)
#guard
  let clipped : PrimState := { clip := some ⟨100, 100, 100, 100⟩ }
  let r := encode #[.backdrop {} ⟨0, 0, 50, 50⟩ 0,
                    .backdrop clipped ⟨0, 0, 50, 50⟩ 8] #[]
  r.snapshotSplit == none && r.cmds.isEmpty && r.backdrops.isEmpty
-- Two backdrops share the one split (all panels frost the same prefix
-- snapshot); a backdrop inside an *offscreen* layer is dropped, but inside
-- an inline-flattened one it keeps its meaning.
#guard
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨100, 100⟩,
                    .backdrop {} ⟨0, 0, 40, 40⟩ 8,
                    .backdrop {} ⟨50, 0, 90, 40⟩ 8] #[]
  r.snapshotSplit == some 1 && r.backdrops.size == 2
    && r.cmds == #[.quads 0 1 none, .backdrop 0 none, .backdrop 1 none]
#guard
  let inner : Prim := .backdrop {} ⟨0, 0, 40, 40⟩ 8
  let off := encode #[.layer {} ⟨0, 0, 40, 40⟩ { alpha := 0.5 } #[inner]] #[]
  let flat := encode #[.layer {} ⟨0, 0, 40, 40⟩ {} #[inner]] #[]
  off.backdrops.isEmpty && off.snapshotSplit == none && off.layers.size == 1
    && flat.backdrops.size == 1 && flat.snapshotSplit == some 0

/-! ## Frame statistics -/

/-- Batch statistics of one encoded frame — the GPU analog of
`tessellationCount` (`Gpu.frameStats` holds the last prepared frame's).
`drawCalls` counts replayed commands across the target pass and every layer
pass; each is one GPU draw. -/
structure FrameStats where
  drawCalls : Nat := 0
  quads : Nat := 0
  shadows : Nat := 0
  meshTriangles : Nat := 0
  glyphs : Nat := 0
  layers : Nat := 0
  images : Nat := 0
  backdrops : Nat := 0
  /-- Pooled offscreen textures alive after this frame's acquire (layer +
  snapshot + backdrop textures) — renderer-set (not part of the pure
  `EncodeResult.stats`), a pool-pressure gauge. -/
  poolTextures : Nat := 0
  deriving Repr, BEq, Inhabited

/-- One-line debug form. -/
def FrameStats.brief (s : FrameStats) : String :=
  s!"draws={s.drawCalls} quads={s.quads} shadows={s.shadows} \
meshTris={s.meshTriangles} glyphs={s.glyphs} layers={s.layers} images={s.images} \
backdrops={s.backdrops} pool={s.poolTextures}"

/-- Compute an encoded frame's statistics (glyph and image quads are 6
indices each). -/
def EncodeResult.stats (r : EncodeResult) : FrameStats :=
  { drawCalls := r.cmds.size + r.layers.foldl (· + ·.cmds.size) 0
    quads := r.quadCount
    shadows := r.shadowCount
    meshTriangles := r.meshIdxCount / 3
    glyphs := r.glyphIdxCount / 6
    layers := r.layers.size
    images := r.imageIdxCount / 6
    backdrops := r.backdrops.size }

-- Merged rects: one draw, two instances.
#guard
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨1, 1⟩, .rect {} .blue ⟨2, 0⟩ ⟨1, 1⟩] #[]
  r.stats == { drawCalls := 1, quads := 2 }
-- A translucent layer: its content draw + the composite draw, one layer.
#guard
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩ { alpha := 0.5 } #[.rect {} .red ⟨10, 10⟩ ⟨4, 4⟩]] #[]
  r.stats == { drawCalls := 2, quads := 1, layers := 1 }
-- Shadows and meshes count their own pipelines.
#guard
  let sh : Prim := .shape {}
    (.rrShadow (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) ⟨0, 2⟩ 4 .black) none
  let arc : Prim := .shape {} (.arcStroke ⟨50, 50⟩ 20 0 3 4 (.solid .blue)) none
  let r := encode #[sh, arc] #[]
  r.stats.shadows == 1 && r.stats.drawCalls == 2
    && r.stats.meshTriangles == r.meshIdxCount / 3 && r.stats.meshTriangles > 0
-- Backdrops count themselves (their composite command is a draw call; the
-- snapshot/blur/blit work is renderer-side, uncounted like blur passes).
#guard
  let r := encode #[.rect {} .red ⟨0, 0⟩ ⟨100, 100⟩, .backdrop {} ⟨0, 0, 40, 40⟩ 8] #[]
  r.stats == { drawCalls := 2, quads := 1, backdrops := 1 }

end Compose.Draw.Gpu

end
