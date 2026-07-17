module

public import Compose.Ui.Draw.DisplayList
public meta import Compose.Ui.Draw.DisplayList
public import Sdl.Render
public meta import Sdl.Render
public import Sdl.Ttf.Text
public meta import Sdl.Ttf.Text

public section

/-!
# Render backend (`Compose/Ui/Draw/Backend.lean`)

The seam between the recorded `DisplayList` and whatever rasterizes it. A
window owns one `RenderBackend` — a bundle of first-class IO ops, so the app
shell never matches on the kind. Create via `SdlBackend.create`
(SDL_Renderer + CPU tessellation, headless-capable, the default) or
`GpuBackend.create` (SDL_GPU SDF shading; real drivers only — lands in
milestone M-b). No direct Compose analog: this is the `Canvas`-provider role
the Android/Desktop `Owner` plays around Skia.
-/

namespace Compose.Draw

/-- Which rendering backend a window uses. -/
inductive RenderBackendKind where
  /-- SDL_Renderer + CPU tessellation (the default; works headless under the
  dummy video driver — all CI runs on it). -/
  | sdlRenderer
  /-- SDL_GPU (GPUI-style SDF shading; real drivers only — SDL_GPU has no
  dummy-driver backend). -/
  | gpu
  deriving Repr, BEq, Inhabited

/-- A per-window rendering backend. -/
structure RenderBackend where
  /-- The backend kind (diagnostics; the ops below are already bound). -/
  kind : RenderBackendKind
  /-- Create the text engine this window's `TextLayout`s shape through
  (`createRendererTextEngine` / `createGpuTextEngine`). -/
  createTextEngine : IO Sdl.Ttf.TextEngine
  /-- Render one frame: clear to `clear`, execute `list`, present. When
  `mayBlock` is `false` the backend must not wait for swapchain availability
  (the live-resize watch's constraint). Returns whether a frame was actually
  presented; `false` re-arms the caller's dirty flag. -/
  render : (clear : Color) → (list : DisplayList) → (mayBlock : Bool) → IO Bool
  /-- Window coordinates → render-target (layout-pixel) coordinates. -/
  coordinatesFromWindow : Float32 → Float32 → IO (Float32 × Float32)
  /-- Best-effort vsync control (the multi-window single-pacer election);
  throws where unsupported — callers `try`/`catch`. -/
  setVSync : Int32 → IO Unit
  /-- The raw SDL renderer when `kind = .sdlRenderer` (the test/screenshot
  escape hatch: `readPixels`, `getVSync`, `coordinatesToWindow`). -/
  sdlRenderer? : Option Sdl.Renderer := none
  /-- Drop device-owned caches (uploaded image textures, pooled layer
  targets, grown frame buffers): after a `renderDeviceReset` (e.g. Android
  resume with a failed EGL restore) their contents are garbage, and on
  `lowMemory` they're the release valve. Everything re-uploads lazily on the
  next frame. Both backends implement this; the GPU backend deliberately
  keeps SDL_ttf's glyph atlases (live `Text` objects reference them, and the
  GPU device survives Android backgrounding, so they never go stale). -/
  invalidateCaches : IO Unit := pure ()
  /-- Release backend resources (GPU: the swapchain claim). Call on window
  teardown, after the composition is disposed. -/
  dispose : IO Unit := pure ()

end Compose.Draw

end
