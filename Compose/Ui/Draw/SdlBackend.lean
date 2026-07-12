import Compose.Ui.Draw.Backend
import Compose.Ui.Draw.Scope
import Sdl

/-!
# SDL backend (`Compose/Ui/Draw/SdlBackend.lean`)

Executes a recorded `DisplayList` against an `SDL_Renderer` — the direct-SDL
emission that used to live inside `DrawScope`, byte-for-byte: solid rects take
the crisp `fillRect` fast path, shapes rasterize their cached mesh (tessellating
on a cache miss) through `Renderer.geometry` with translation/alpha folded into
the vertices, text runs draw through the renderer text engine, and the resolved
rect clip is applied to SDL's single render clip rect only when it changes
between primitives. Layers flatten by folding their alpha into the content
(the documented double-blend approximation; the GPU backend composites them
offscreen instead). Works headless under the dummy video driver — the whole
test suite runs on this backend.
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

/-- Convert a `Mesh` (local coordinates) to SDL geometry, folding in the
primitive's `origin` translation and `alpha`. Feather vertices keep alpha `0`
after scaling; the index buffer is already `Int32`-encoded and passes through
untouched.

Positions are rounded to whole pixels: SDL's software rasterizer truncates
geometry vertices to integer coordinates internally (`SW_QueueGeometry`'s
`(int)` cast feeding the half-pixel fixed-point triangle filler), which makes
sub-pixel band seams — the fill tessellator's trapezoid boundaries at curve
event ys, a stroke's cap-arc bands — drop or double whole pixel rows.
Rounding first is the closest integer approximation of true pixel-center
coverage (a quad snapped to `[y0, y1]` rasterizes exactly rows
`[round y0, round y1)`), so abutting bands stay gap-free and the result
tracks the GPU backend's exact fractional rasterization within half a pixel. -/
private def meshToGeometry (m : Mesh) (translation : Offset) (alpha : Float32) :
    Array Sdl.Vertex × Array Int32 :=
  let snap (x : Float32) : Float32 := (x + 0.5).floor
  let verts := m.vertices.map fun v =>
    ({ position := ⟨snap (v.pos.x + translation.x), snap (v.pos.y + translation.y)⟩
       color := ⟨v.color.r, v.color.g, v.color.b, v.color.a * alpha⟩
       texCoord := ⟨0, 0⟩ } : Sdl.Vertex)
  (verts, m.indices)

/-- Apply `clip` to SDL's single render clip rect iff it differs from the
currently applied one (tracked in `applied`). -/
private def applyClip (r : Renderer) (applied : IO.Ref (Option Rect))
    (clip : Option Rect) : IO Unit := do
  if (← applied.get) != clip then
    r.setClipRect (clip.map toSdlRect)
    applied.set clip

/-- Rasterize a mesh through `Renderer.geometry` (no-op when empty). -/
private def emitMesh (r : Renderer) (m : Mesh) (origin : Offset) (alpha : Float32) : IO Unit := do
  if m.isEmpty then return
  let (verts, idx) := meshToGeometry m origin alpha
  r.setDrawBlendMode .blend
  r.geometry none verts idx

/-- Execute one primitive; `extraAlpha` is the flattened alpha of enclosing
`layer`s. -/
private partial def execPrim (r : Renderer) (applied : IO.Ref (Option Rect))
    (extraAlpha : Float32) : Prim → IO Unit
  | .rect st color topLeft size => do
    applyClip r applied st.clip
    let col := color.withAlpha (color.a * st.alpha * extraAlpha)
    let (cr, cg, cb, ca) := col.toBytes
    let tl := topLeft + st.origin
    r.setDrawBlendMode .blend
    r.setDrawColor cr cg cb ca
    r.fillRect (some ⟨tl.x, tl.y, size.width, size.height⟩)
  | .shape st spec cached => do
    applyClip r applied st.clip
    emitMesh r (cached.getD spec.tessellate) st.origin (st.alpha * extraAlpha)
  | .mesh st m => do
    applyClip r applied st.clip
    emitMesh r m st.origin (st.alpha * extraAlpha)
  | .text st run => do
    applyClip r applied st.clip
    let c := run.color
    run.text.setColorFloat ⟨c.r, c.g, c.b, c.a * st.alpha * extraAlpha⟩
    run.text.drawRenderer st.origin.x st.origin.y
  | .layer _ _ alpha content => do
    -- Flatten: fold the layer alpha into the content (today's double-blend
    -- approximation of group opacity; DESIGN.md). The GPU backend composites
    -- a real offscreen layer instead.
    for p in content do
      execPrim r applied (extraAlpha * alpha) p

/-- Execute a recorded display list against `r`, restoring an unclipped
renderer afterwards. -/
def execute (r : Renderer) (list : DisplayList) : IO Unit := do
  let applied ← IO.mkRef (none : Option Rect)
  for p in list do
    execPrim r applied 1.0 p
  applyClip r applied none

/-- Package `renderer` as a `RenderBackend` (see `Backend.lean`): render =
clear → execute → present (always presents — SDL_Renderer never blocks on
acquire). -/
def create (renderer : Renderer) : RenderBackend where
  kind := .sdlRenderer
  createTextEngine := Sdl.Ttf.createRendererTextEngine renderer
  render := fun clear list _mayBlock => do
    let (cr, cg, cb, ca) := clear.toBytes
    renderer.setDrawColor cr cg cb ca
    renderer.clear
    execute renderer list
    renderer.present
    return true
  coordinatesFromWindow := fun x y => renderer.coordinatesFromWindow x y
  setVSync := fun target => renderer.setVSync target
  sdlRenderer? := some renderer
  dispose := pure ()

end SdlBackend

/-- Record `body` and execute it against `renderer` in one go — the
single-shot entry point low-level draw tests use (the app shell records via
`DrawScope.record` and renders through its window's `RenderBackend` instead). -/
def DrawScope.run (renderer : Renderer) (density : Density := {}) (body : DrawM α) : IO α := do
  let (list, a) ← DrawScope.record density body
  SdlBackend.execute renderer list
  return a

end Compose.Draw
