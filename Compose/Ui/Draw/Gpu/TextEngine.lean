module

public import Compose.Ui.Draw.DisplayList
public meta import Compose.Ui.Draw.DisplayList
public import Compose.Ui.Draw.Gpu.Instance
public meta import Compose.Ui.Draw.Gpu.Instance

public section

/-!
# GPU text resolution (`Compose/Ui/Draw/Gpu/TextEngine.lean`)

The IO half of the GPU text path: before the pure encode, the renderer walks
the display list and fetches every text run's `Text.gpuDrawData` (SDL_ttf's
GPU atlas quads — an IO snapshot of live atlas state). Each sequence's atlas
texture goes into a per-frame texture table; the encoder sees only plain
`ResolvedRun` data with atlas *indices*, and the replay binds the table
entries. The walk order here (list order, recursing into layer content) is
exactly the encoder's walk order — the two consume runs by position.

Each window's `TextEngine` itself is created by the backend facade
(`Sdl.Ttf.createGpuTextEngine` on the shared device); the recorded
`Ttf.Text` handles already carry their engine.
-/

namespace Compose.Draw.Gpu
open Compose.Draw

private partial def collect (runs : IO.Ref (Array ResolvedRun))
    (atlases : IO.Ref (Array Sdl.Gpu.Texture)) : Prim → IO Unit
  | .text _ run => do
    let data ← run.text.gpuDrawData
    let mut seqs : ResolvedRun := #[]
    for s in data do
      let idx := (← atlases.get).size
      atlases.modify (·.push s.atlasTexture)
      seqs := seqs.push
        { atlas := idx, xy := s.xy, uv := s.uv
          indices := s.indices, imageType := s.imageType }
    runs.modify (·.push seqs)
  | .layer _ _ _ content => do
    for p in content do
      collect runs atlases p
  | _ => pure ()

/-- Resolve every text run in `list` (walk order = encode order): the runs'
atlas draw data plus the frame's atlas texture table the sequences index. -/
def resolveTexts (list : DisplayList) : IO (Array ResolvedRun × Array Sdl.Gpu.Texture) := do
  let runs ← IO.mkRef (#[] : Array ResolvedRun)
  let atlases ← IO.mkRef (#[] : Array Sdl.Gpu.Texture)
  for p in list do
    collect runs atlases p
  return (← runs.get, ← atlases.get)

end Compose.Draw.Gpu

end
