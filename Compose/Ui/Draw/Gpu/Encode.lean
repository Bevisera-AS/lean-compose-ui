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
- `layer` → flattened with folded alpha in M-b (the SDL approximation);
  offscreen compositing lands in M-c.

Clips: `PrimState.clip` becomes an integer scissor per command with the same
floor/ceil expansion as the SDL backend's clip rect, so the two backends clip
identically in M-b (`QuadInstance`'s in-shader rounded mask takes over on the
GPU in M-c). Consecutive commands with equal kind/scissor/atlas merge.
-/

namespace Compose.Draw.Gpu
open Compose.Draw

/-- Encoder output: one packed buffer per pipeline plus the replay commands.
`textsConsumed` is the number of text runs consumed (walk-order bookkeeping). -/
structure EncodeResult where
  /-- Packed `QuadInstance`s (`quadStride` bytes each). -/
  quads : ByteArray := .empty
  quadCount : Nat := 0
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
  | .circleFillClipped .. | .arcStroke .. => none

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

/-! ## The walk -/

/-- Encode one primitive (recursing into layers with folded alpha). -/
private partial def encodePrim (texts : Array ResolvedRun) (extraAlpha : Float32)
    (st : EncodeResult) : Prim → EncodeResult
  | .rect s color topLeft size =>
    if size.isEmpty then st
    else
      let alpha := s.alpha * extraAlpha
      pushQuad st
        { origin := s.origin + topLeft, size
          bg0 := color.withAlpha (color.a * alpha)
          bg1 := color.withAlpha (color.a * alpha) }
        (scissorOf s.clip)
  | .shape s spec cached =>
    let alpha := s.alpha * extraAlpha
    let scissor := scissorOf s.clip
    match lowerShape spec with
    | some q => pushQuad st (placeQuad q s.origin alpha) scissor
    | none => pushMesh st (cached.getD spec.tessellate) s.origin alpha scissor
  | .mesh s m => pushMesh st m s.origin (s.alpha * extraAlpha) (scissorOf s.clip)
  | .text s run =>
    let runIdx := st.textsConsumed
    let st := { st with textsConsumed := runIdx + 1 }
    match texts[runIdx]? with
    | none => st
    | some seqs =>
      -- Snap once per run in device px (the shimmer fix): intra-run subpixel
      -- layout is preserved, the run origin lands on the pixel grid.
      let origin : Offset := ⟨s.origin.x.round, s.origin.y.round⟩
      seqs.foldl (pushGlyphSeq run.color (s.alpha * extraAlpha) origin (scissorOf s.clip)) st
  | .layer _ _ alpha content =>
    content.foldl (encodePrim texts (extraAlpha * alpha)) st

/-- Encode a display list against its resolved text runs (in the same
prim-walk order `Gpu.resolveTexts` produced them). -/
def encode (list : DisplayList) (texts : Array ResolvedRun) : EncodeResult :=
  list.foldl (encodePrim texts 1.0) {}

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
-- Layer content flattens with folded alpha (M-b): same instance count, and
-- the folded quad differs from the unfolded one only in its packed alpha.
#guard
  let inner : Prim := .rect {} .red ⟨0, 0⟩ ⟨4, 4⟩
  let r := encode #[.layer {} ⟨0, 0, 4, 4⟩ 0.5 #[inner]] #[]
  let plain := encode #[inner] #[]
  r.quadCount == 1 && r.cmds == #[.quads 0 1 none] && r.quads != plain.quads
-- Consecutive meshes merge into one indexed draw with absolute indices.
#guard
  let arc : Prim := .shape {} (.arcStroke ⟨50, 50⟩ 20 0 3 4 (.solid .blue)) none
  let r := encode #[arc, arc] #[]
  r.cmds.size == 1 && (match r.cmds[0]! with | .mesh 0 n none => n == r.meshIdxCount | _ => false)

end Compose.Draw.Gpu
