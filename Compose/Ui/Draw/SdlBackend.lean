module

public import Compose.Ui.Draw.Backend
public meta import Compose.Ui.Draw.Backend
public import Compose.Ui.Draw.Scope
public meta import Compose.Ui.Draw.Scope
public import Sdl
public meta import Sdl

public section

/-!
# SDL backend (`Compose/Ui/Draw/SdlBackend.lean`)

Executes a recorded `DisplayList` against an `SDL_Renderer` — the direct-SDL
emission that used to live inside `DrawScope`, byte-for-byte: solid rects take
the crisp `fillRect` fast path, shapes rasterize their cached mesh (tessellating
on a cache miss) through `Renderer.geometryPacked` with translation/alpha folded
into the vertices and the index buffer pre-packed at cache time, text runs draw through the renderer text engine at the shared
snapped run origin (`snapTextOrigin` — byte-identical to the GPU backend at
any origin, no fractional-origin shimmer), images draw
through per-backend cached textures (`createTextureFromSurface` on first use of
an `ImageBitmap.id`, never evicted — textures die with the renderer), and the
resolved rect clip is applied to SDL's single render clip rect only when it
changes between primitives.

Untransformed layers flatten by folding their alpha into the content (the
documented double-blend approximation; the GPU backend composites all layers
offscreen). *Transformed* layers render for real: content draws into a pooled
render-target texture (cleared transparent — `.blend` onto transparency
yields premultiplied texels), then one `textureAffine` composite maps the
region's corners through the layer transform with `.blendPremultiplied` and
the group alpha as color+alpha mod (scaling all four premultiplied channels).
SDL clip state is per render target, so the clip tracker resets across every
`setTarget`. Layer *effects*: `LayerEffect.blur` is ignored — content
renders unblurred on this backend (a documented approximation, like the
rounded-clip story; a CPU Gaussian on the software path buys nothing the GPU
backend doesn't already verify) — while `LayerEffect.stretch` approximates
as a uniform scale anchored at the pinned edge (Flutter's non-shader
fallback) through the transformed-layer path, so overscroll stays visible
here too. Works headless under the dummy video driver — the whole test
suite runs on this backend.
-/

namespace Compose.Draw
open Sdl

namespace SdlBackend

/-- Convert a float `Rect` to an integer `Sdl.Rect`, expanding to whole pixels
(floor the min corner, ceil the max corner) so the clip fully covers the region.
Width/height are clamped non-negative. -/
private def toSdlRect (r : Rect) : Sdl.Rect :=
  let l := r.left.floor.toInt32
  let t := r.top.floor.toInt32
  let rt := r.right.ceil.toInt32
  let bt := r.bottom.ceil.toInt32
  ⟨l, t, max 0 (rt - l), max 0 (bt - t)⟩

/-- Convert a `Mesh`'s vertices (local coordinates) to SDL geometry vertices,
folding in the primitive's `origin` translation and `alpha`. Feather vertices
keep alpha `0` after scaling; the index buffer is not touched here — it
travels pre-packed (`Mesh.packIndices`).

Positions are rounded to whole pixels: SDL's software rasterizer truncates
geometry vertices to integer coordinates internally (`SW_QueueGeometry`'s
`(int)` cast feeding the half-pixel fixed-point triangle filler), which makes
sub-pixel band seams — the fill tessellator's trapezoid boundaries at curve
event ys, a stroke's cap-arc bands — drop or double whole pixel rows.
Rounding first is the closest integer approximation of true pixel-center
coverage (a quad snapped to `[y0, y1]` rasterizes exactly rows
`[round y0, round y1)`), so abutting bands stay gap-free and the result
tracks the GPU backend's exact fractional rasterization within half a pixel. -/
private def meshVertices (m : Mesh) (translation : Offset) (alpha : Float32) :
    Array Sdl.Vertex :=
  let snap (x : Float32) : Float32 := (x + 0.5).floor
  m.vertices.map fun v =>
    ({ position := ⟨snap (v.pos.x + translation.x), snap (v.pos.y + translation.y)⟩
       color := ⟨v.color.r, v.color.g, v.color.b, v.color.a * alpha⟩
       texCoord := ⟨0, 0⟩ } : Sdl.Vertex)

/-- One pooled render-target texture for offscreen layers (64 px-quantized
dimensions, like the GPU backend's layer pool). -/
private structure TargetEntry where
  tex : Texture
  w : Int32
  h : Int32
  /-- Executed frames since last use (released past `poolTrimAge`). -/
  idle : Nat := 0
  /-- Claimed by an enclosing in-progress layer (nesting). -/
  inUse : Bool := false

/-- Executed frames a pooled target texture may sit idle before release. -/
private def poolTrimAge : Nat := 120

/-- Per-backend texture caches: the image texture cache (`ImageBitmap.id` →
the uploaded texture; never evicted — images are immutable and id-keyed) and
the render-target pool for transformed layers. Both die with the renderer. -/
structure Caches where private mk ::
  private images : IO.Ref (Array (Nat × Texture))
  private targets : IO.Ref (Array TargetEntry)

/-- Fresh, empty caches. -/
def Caches.new : IO Caches :=
  return ⟨← IO.mkRef #[], ← IO.mkRef #[]⟩

/-- Drop everything (`RenderBackend.invalidateCaches`): image textures
re-upload on next use, pooled targets are recreated on demand; the dropped
`Texture`s are destroyed by their finalizers. -/
def Caches.clear (c : Caches) : IO Unit := do
  c.images.set #[]
  c.targets.set #[]

/-- The cached texture for `img`, uploading via `createTextureFromSurface` on
first use (blend mode set once — the straight-alpha surface becomes a
blendable texture). -/
private def obtainTexture (r : Renderer) (cache : Caches)
    (img : ImageBitmap) : IO Texture := do
  let entries ← cache.images.get
  for (id, tex) in entries do
    if id == img.id then
      return tex
  let tex ← r.createTextureFromSurface img.surface
  tex.setBlendMode .blend
  cache.images.modify (·.push (img.id, tex))
  return tex

/-- Quantize a (whole-px, positive) layer extent up to a multiple of 64. -/
private def quantize64 (x : Float32) : Int32 :=
  let n := max 1 x.toInt32
  (n + 63) / 64 * 64

/-- Claim a pooled `.target` texture of at least `w × h` px (first-fit ≥ the
quantized request, creating an `rgba32` target on miss). Returns the texture
with its pool index — release with `releaseTarget` once composited; siblings
then reuse it within the frame, so the pool's steady size is the layer
nesting depth. -/
private def acquireTarget (r : Renderer) (cache : Caches) (w h : Float32) :
    IO (Texture × Nat) := do
  let qw := quantize64 w
  let qh := quantize64 h
  let entries ← cache.targets.get
  let mut found : Option (Nat × Texture) := none
  let mut j := 0
  for e in entries do
    if found.isNone && !e.inUse && e.w ≥ qw && e.h ≥ qh then
      found := some (j, e.tex)
    j := j + 1
  match found with
  | some (i, tex) =>
    cache.targets.modify (·.modify i ({ · with inUse := true, idle := 0 }))
    return (tex, i)
  | none =>
    let tex ← r.createTexture .rgba32 .target qw qh
    cache.targets.modify (·.push { tex, w := qw, h := qh, inUse := true })
    return (tex, entries.size)

/-- Return a pooled target to the free list. -/
private def releaseTarget (cache : Caches) (i : Nat) : IO Unit :=
  cache.targets.modify (·.modify i ({ · with inUse := false }))

/-- Age the pool one executed frame and release entries idle past
`poolTrimAge`. -/
private def trimTargets (cache : Caches) : IO Unit := do
  let mut kept : Array TargetEntry := #[]
  for e in (← cache.targets.get) do
    if e.inUse then
      kept := kept.push e
    else if e.idle + 1 ≥ poolTrimAge then
      e.tex.destroy
    else
      kept := kept.push { e with idle := e.idle + 1 }
  cache.targets.set kept

/-- Apply `clip` to SDL's single render clip rect iff it differs from the
currently applied one (tracked in `applied`). -/
private def applyClip (r : Renderer) (applied : IO.Ref (Option Rect))
    (clip : Option Rect) : IO Unit := do
  if (← applied.get) != clip then
    r.setClipRect (clip.map toSdlRect)
    applied.set clip

/-- Rasterize a mesh through `Renderer.geometryPacked` (no-op when empty).
Vertices transform and pack per emit — origin/alpha vary with the frame —
while `idxBytes` arrives pre-packed (`Mesh.packed` for cached shapes, packed
on the spot for immediate meshes). -/
private def emitMesh (r : Renderer) (m : Mesh) (idxBytes : ByteArray)
    (origin : Offset) (alpha : Float32) : IO Unit := do
  if m.isEmpty then return
  r.setDrawBlendMode .blend
  r.geometryPacked none (packVertices (meshVertices m origin alpha)) idxBytes

/-- Execute one primitive. `extraAlpha` is the flattened alpha of enclosing
untransformed `layer`s; `shift` displaces record-time coordinates into the
current render target's (zero on the main target; a layer region's negated
origin inside its texture — always integral, since layer regions snap to
whole px). -/
private partial def execPrim (r : Renderer) (applied : IO.Ref (Option Rect))
    (caches : Caches) (extraAlpha : Float32) (shift : Offset) : Prim → IO Unit
  | .rect st color topLeft size => do
    applyClip r applied (st.clip.map (·.translate shift))
    let col := color.withAlpha (color.a * st.alpha * extraAlpha)
    let (cr, cg, cb, ca) := col.toBytes
    let tl := topLeft + st.origin + shift
    r.setDrawBlendMode .blend
    r.setDrawColor cr cg cb ca
    r.fillRect (some ⟨tl.x, tl.y, size.width, size.height⟩)
  | .shape st spec cached => do
    applyClip r applied (st.clip.map (·.translate shift))
    let pm := cached.getD spec.tessellate.packed
    emitMesh r pm.mesh pm.idxBytes (st.origin + shift) (st.alpha * extraAlpha)
  | .mesh st m => do
    applyClip r applied (st.clip.map (·.translate shift))
    emitMesh r m m.packIndices (st.origin + shift) (st.alpha * extraAlpha)
  | .text st run => do
    applyClip r applied (st.clip.map (·.translate shift))
    let c := run.color
    run.text.setColorFloat ⟨c.r, c.g, c.b, c.a * st.alpha * extraAlpha⟩
    -- Snap the run origin like the GPU backend (`snapTextOrigin`): fractional
    -- origins rasterize identically across backends and never shimmer.
    let o := snapTextOrigin st.origin shift
    run.text.drawRenderer o.x o.y
  | .image st img src dst sampling => do
    applyClip r applied (st.clip.map (·.translate shift))
    let tex ← obtainTexture r caches img
    -- Per-draw (mod state persists per texture): the sampling mode and the
    -- resolved alpha.
    tex.setScaleMode (match sampling with | .nearest => .nearest | .linear => .linear)
    tex.setColorModFloat 1 1 1
    tex.setAlphaModFloat (st.alpha * extraAlpha)
    let d := dst.translate (st.origin + shift)
    let toF (x : Rect) : Sdl.FRect := ⟨x.left, x.top, x.width, x.height⟩
    r.texture tex (src.map toF) (some (toF d))
  | .layer st bounds props content => do
    -- The stretch approximation (Flutter's non-shader fallback, AOSP's
    -- `StretchEffect.makeLinearStretch`): a uniform scale `(1 + |s|)`
    -- anchored at the pinned edge, composed into the layer transform — the
    -- enclosing (scroll) clip crops the overdraw. The GPU backend runs the
    -- true non-linear warp instead; the visual difference at overscroll's
    -- ≤ 3.2% intensities is slight (distant content moves proportionally
    -- rather than easing off).
    let transform := match props.effect.normalize with
      | .stretch sx sy =>
        let ax := if sx > 0 then bounds.left else bounds.right
        let ay := if sy > 0 then bounds.top else bounds.bottom
        let scale := (Affine.translation ⟨ax, ay⟩).comp
          ((Affine.scaling (1 + sx.abs) (1 + sy.abs)).comp
            (Affine.translation ⟨-ax, -ay⟩))
        some (scale.comp (props.transform.getD .identity))
      | _ => props.transform
    match transform with
    | none =>
      -- Flatten: fold the layer alpha into the content (the documented
      -- double-blend approximation of group opacity; DESIGN.md). The GPU
      -- backend composites a real offscreen layer instead.
      for p in content do
        execPrim r applied caches (extraAlpha * props.alpha) shift p
    | some t => do
      -- Real offscreen layer: content region = bounds plus a 1 px AA margin,
      -- snapped to whole px (the GPU encoder's rule).
      let l := (bounds.left - 1).floor
      let tp := (bounds.top - 1).floor
      let rt := max ((bounds.right + 1).ceil) (l + 1)
      let bt := max ((bounds.bottom + 1).ceil) (tp + 1)
      let (w, h) := (rt - l, bt - tp)
      let (tex, poolIdx) ← acquireTarget r caches w h
      let prevTarget ← r.getTarget
      let savedClip ← applied.get
      r.setTarget (some tex)
      -- Clip state is per render target, and pooled textures can carry a
      -- stale clip from their previous use: reset both SDL and the tracker.
      r.setClipRect none
      applied.set none
      -- Transparent clear (`clear` ignores blend mode): `.blend` content on
      -- transparency yields premultiplied texels.
      r.setDrawColor 0 0 0 0
      r.clear
      -- Content renders at full alpha; the group alpha (and any enclosing
      -- flattened alpha) applies once at composite — transformed layers get
      -- true group opacity on SDL.
      for p in content do
        execPrim r applied caches 1.0 (shift - ⟨l, tp⟩) p
      r.setTarget prevTarget
      -- The previous target's clip state was untouched (per-target): just
      -- restore the tracker.
      applied.set savedClip
      applyClip r applied (st.clip.map (·.translate shift))
      let a := props.alpha * extraAlpha
      tex.setBlendMode .blendPremultiplied
      tex.setColorModFloat a a a
      tex.setAlphaModFloat a
      -- Region corners mapped through the transform, in this target's
      -- coordinates.
      let map (p : Offset) : Offset := t.mapOffset p + shift
      let o := map ⟨l, tp⟩
      if t.snapComposite then
        -- Near-integer pure translation: snap to the grid and copy 1:1 —
        -- crisp (text stays byte-identical to unlayered rendering).
        tex.setScaleMode .nearest
        r.texture tex (some ⟨0, 0, w, h⟩) (some ⟨o.x.round, o.y.round, w, h⟩)
      else
        tex.setScaleMode .linear
        let rgt := map ⟨rt, tp⟩
        let dwn := map ⟨l, bt⟩
        r.textureAffine tex (some ⟨0, 0, w, h⟩)
          (some ⟨o.x, o.y⟩) (some ⟨rgt.x, rgt.y⟩) (some ⟨dwn.x, dwn.y⟩)
      releaseTarget caches poolIdx

/-- Execute a recorded display list against `r`, restoring an unclipped
renderer afterwards. `caches` is the backend's persistent texture state
(pass a fresh `Caches.new` for single-shot execution). -/
def execute (r : Renderer) (list : DisplayList) (caches : Caches) :
    IO Unit := do
  let applied ← IO.mkRef (none : Option Rect)
  for p in list do
    execPrim r applied caches 1.0 .zero p
  applyClip r applied none
  trimTargets caches

/-- Package `renderer` as a `RenderBackend` (see `Backend.lean`): render =
clear → execute → present (always presents — SDL_Renderer never blocks on
acquire). -/
def create (renderer : Renderer) : IO RenderBackend := do
  let images ← Caches.new
  return {
    kind := .sdlRenderer
    createTextEngine := Sdl.Ttf.createRendererTextEngine renderer
    render := fun clear list _mayBlock => do
      let (cr, cg, cb, ca) := clear.toBytes
      renderer.setDrawColor cr cg cb ca
      renderer.clear
      execute renderer list images
      renderer.present
      return true
    coordinatesFromWindow := fun x y => renderer.coordinatesFromWindow x y
    setVSync := fun target => renderer.setVSync target
    sdlRenderer? := some renderer
    invalidateCaches := images.clear
    dispose := pure () }

end SdlBackend

/-- Record `body` and execute it against `renderer` in one go — the
single-shot entry point low-level draw tests use (the app shell records via
`DrawScope.record` and renders through its window's `RenderBackend` instead). -/
def DrawScope.run (renderer : Renderer) (density : Density := {}) (body : DrawM α) : IO α := do
  let (list, a) ← DrawScope.record density body
  SdlBackend.execute renderer list (← SdlBackend.Caches.new)
  return a

end Compose.Draw

end
