import Compose.Ui.Draw.DisplayList
import Compose.Ui.Draw.Gpu.Instance

/-!
# GPU display-list encoder (`Compose/Ui/Draw/Gpu/Encode.lean`)

Pure lowering of a recorded `DisplayList` into the GPU pipelines' packed
buffers plus a flat `DrawCmd` list, replayed back-to-front by
`Gpu/Renderer.lean`. Text runs arrive pre-resolved (`ResolvedRun`, fetched in
IO by `Gpu/TextEngine.lean` in the same prim-walk order this encoder consumes
them).

Lowering per primitive:
- `rect`, and `shape` specs that are axis-aligned rounded geometry under a
  solid or two-stop-gradient brush (`rrFill`/`rrStroke`, circles, axis-aligned
  lines) → **quad instances** (SDF coverage in the fragment shader).
- Everything else (`arcStroke`, angled lines, the ripple's
  `circleFillClipped`, multi-stop or gradient-stroked brushes) → the **mesh
  pipeline**, reusing the exact CPU tessellation the SDL backend rasterizes.
- `text` → **glyph vertices** (atlas quads snapped once per run at the
  rounded run origin — the shimmer fix; SDL_ttf's y-up data maps as
  `screen = origin + (x, −y)`, probe-verified).
- `rrShadow` → **shadow instances** (the analytic Gaussian shader; blur `≤ 0`
  degrades to a hard offset fill quad, matching the tessellator).
- `layer` (alpha `< 1`) → an **offscreen layer pass**: the content encodes
  into its own command list with every coordinate shifted to the layer's
  origin (`LayerEnc`; packed buffers are shared across passes), and the
  parent list gets one `.layer` composite command. The composite region is
  the recorded bounds ∩ clip plus a 1 px AA margin, snapped to whole px so
  pixel-grid reasoning (text snapping) holds inside. Alpha `≥ 1` flattens
  inline. Layers are emitted innermost-first — the render order.

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
  /-- Composite region (whole-px `Rect`). -/
  bounds : Rect
  /-- Group alpha applied once at composite. -/
  alpha : Float32
  /-- The layer's own render-pass commands. -/
  cmds : Array DrawCmd
  deriving Repr, BEq, Inhabited

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
  /-- Draws in paint order. -/
  cmds : Array DrawCmd := #[]
  /-- Offscreen layers, innermost-first (their render order; `DrawCmd.layer`
  indices point here). -/
  layers : Array LayerEnc := #[]
  /-- Text runs consumed so far. -/
  textsConsumed : Nat := 0

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
`SdlBackend.meshToGeometry`; indices are rebased to absolute so consecutive
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
  -- testgputext convention. `.alpha` (and `.sdf`) tint with the run color.
  let vcolor := match seq.imageType with
    | .color => Color.white.withAlpha alpha
    | _ => color.withAlpha (color.a * alpha)
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

/-! ## Shape lowering -/

/-- Lower a brush to the quad fill encoding: gradient endpoints plus the
projection vector (`t = saturate(dot(p - start, dir))`, `dir` scaled by
`1/len²`). Solid → equal endpoints, zero projection. `none` = the brush needs
the mesh path (≠ 2 stops, or a degenerate axis). Coordinates stay local; the
caller translates by the primitive origin. -/
private def quadBrush : Brush → Option (Color × Color × Offset × Offset)
  | .solid c => some (c, c, .zero, .zero)
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
    some (c0, c1, s, ⟨d.x / len2, d.y / len2⟩)

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
    let (bg0, bg1, gs, gd) ← quadBrush brush
    let (o, sz, (tl, tr, br, bl)) := rrQuad rr
    some { origin := o, size := sz, radiusTL := tl, radiusTR := tr
           radiusBR := br, radiusBL := bl, bg0, bg1, gradStart := gs, gradDir := gd }
  | .rrStroke rr width brush =>
    match brush with
    | .solid c =>
      let (o, sz, (tl, tr, br, bl)) := rrQuad rr
      some { origin := o, size := sz, radiusTL := tl, radiusTR := tr
             radiusBR := br, radiusBL := bl, borderColor := c, borderWidth := width }
    | _ => none
  | .circleFill center radius brush => do
    let (bg0, bg1, gs, gd) ← quadBrush brush
    some { origin := ⟨center.x - radius, center.y - radius⟩
           size := ⟨radius * 2, radius * 2⟩
           radiusTL := radius, radiusTR := radius, radiusBR := radius, radiusBL := radius
           bg0, bg1, gradStart := gs, gradDir := gd }
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
`alpha ≥ 1` layers. -/
private partial def encodePrim (texts : Array ResolvedRun) (extraAlpha : Float32)
    (shift : Offset) (st : EncodeResult) : Prim → EncodeResult
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
      | some (bg0, bg1, gs, gd) =>
        let q : QuadInstance :=
          { origin := ⟨center.x - radius, center.y - radius⟩
            size := ⟨radius * 2, radius * 2⟩
            radiusTL := radius, radiusTR := radius
            radiusBR := radius, radiusBL := radius
            bg0, bg1, gradStart := gs, gradDir := gd }
        pushQuad st (maskQuadRR (placeQuad q origin alpha) (rr.translate origin)) scissor
      | none => pushMesh st (cached.getD spec.tessellate) origin alpha scissor
    | _ =>
      match lowerShape spec with
      | some q => pushQuad st (maskQuad (placeQuad q origin alpha) s.rounded shift) scissor
      | none => pushMesh st (cached.getD spec.tessellate) origin alpha scissor
  | .mesh s m => pushMesh st m (s.origin + shift) (s.alpha * extraAlpha) (scissorAt s.clip shift)
  | .text s run =>
    let runIdx := st.textsConsumed
    let st := { st with textsConsumed := runIdx + 1 }
    match texts[runIdx]? with
    | none => st
    | some seqs =>
      -- Snap once per run in device px (the shimmer fix): intra-run subpixel
      -- layout is preserved, the run origin lands on the pixel grid (`shift`
      -- is integral, so snapping commutes with the layer displacement).
      let origin : Offset := ⟨(s.origin.x + shift.x).round, (s.origin.y + shift.y).round⟩
      seqs.foldl (pushGlyphSeq run.color (s.alpha * extraAlpha) origin (scissorAt s.clip shift)) st
  | .layer s bounds alpha content =>
    if alpha ≥ 1.0 then
      -- No compositing needed: flatten inline (records don't produce these;
      -- hand-built lists may).
      content.foldl (encodePrim texts (extraAlpha * alpha) shift) st
    else Id.run do
      -- Composite region: bounds ∩ clip plus a 1 px AA margin, snapped to
      -- whole px (kept ≥ 1×1 even when degenerate so the text-run walk stays
      -- aligned with `resolveTexts`).
      let r := match s.clip with
        | some c => Rect.intersect bounds c
        | none => bounds
      let l := (r.left + shift.x - 1).floor
      let t := (r.top + shift.y - 1).floor
      let rt := max ((r.right + shift.x + 1).ceil) (l + 1)
      let bt := max ((r.bottom + shift.y + 1).ceil) (t + 1)
      let saved := st.cmds
      let st := content.foldl (encodePrim texts extraAlpha (shift - ⟨l, t⟩))
        { st with cmds := #[] }
      let idx := st.layers.size
      return { st with
        cmds := saved.push (.layer idx (scissorAt s.clip shift))
        layers := st.layers.push
          { bounds := ⟨l, t, rt, bt⟩, alpha := alpha * extraAlpha, cmds := st.cmds } }

/-- Encode a display list against its resolved text runs (in the same
prim-walk order `Gpu.resolveTexts` produced them). -/
def encode (list : DisplayList) (texts : Array ResolvedRun) : EncodeResult :=
  list.foldl (encodePrim texts 1.0 .zero) {}

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
-- A full-alpha layer flattens inline (no offscreen pass).
#guard
  let inner : Prim := .rect {} .red ⟨0, 0⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨0, 0, 4, 4⟩ 1.0 #[inner]] #[]
  r.quadCount == 1 && r.cmds == #[.quads 0 1 none] && r.layers.isEmpty
-- A translucent layer becomes an offscreen pass: bounds get the 1 px AA
-- margin and whole-px snap, content coordinates shift to the layer origin,
-- and the parent list holds one composite command.
#guard
  let inner : Prim := .rect {} .red ⟨10, 10⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨8, 8, 24, 24⟩ 0.5 #[inner]] #[]
  r.layers.size == 1 && r.cmds == #[.layer 0 none]
    && r.layers[0]!.bounds == (⟨7, 7, 25, 25⟩ : Rect) && r.layers[0]!.alpha == 0.5
    && r.layers[0]!.cmds == #[.quads 0 1 none]
    && r.quads == (encode #[.rect {} .red ⟨3, 3⟩ ⟨4, 4⟩] #[]).quads
-- Nested layers emit innermost-first; the outer layer composites the inner.
#guard
  let inner : Prim := .layer {} ⟨0, 0, 4, 4⟩ 0.5 #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]
  let r := encode #[.layer {} ⟨0, 0, 8, 8⟩ 0.25 #[inner]] #[]
  r.layers.size == 2 && r.cmds == #[.layer 1 none]
    && r.layers[1]!.cmds == #[.layer 0 none] && r.layers[0]!.alpha == 0.5
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

end Compose.Draw.Gpu
