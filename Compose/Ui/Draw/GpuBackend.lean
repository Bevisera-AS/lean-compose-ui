module

public import Compose.Ui.Draw.Backend
public meta import Compose.Ui.Draw.Backend
public import Compose.Ui.Draw.Gpu.Renderer
public meta import Compose.Ui.Draw.Gpu.Renderer

public section

/-!
# GPU backend facade (`Compose/Ui/Draw/GpuBackend.lean`)

Packages the GPU renderer (`Compose/Ui/Draw/Gpu/`) as a `RenderBackend`:
SDL_GPU on the process-shared device, SDL_ttf's GPU text engine, swapchain
present-mode selection for the vsync hook. Real drivers only (SDL_GPU has no
dummy-video backend) — `Compose.makeBackend` falls back to the SDL renderer
with a warning when device creation throws. The default backend; opt out
with `COMPOSE_BACKEND=sdl` or `AppConfig.backend := some .sdlRenderer`.
-/

namespace Compose.Draw

namespace GpuBackend

/-- Map the SDL-renderer vsync convention (`1`/`-1` = synced, `0` = don't
wait) to swapchain present modes: synced → `.vsync`; unsynced prefers
`.mailbox`, then `.immediate`, then stays `.vsync` (macOS Metal supports
vsync + immediate but not mailbox, probe-verified). -/
private def applyVSync (dev : Sdl.Gpu.Device) (window : Sdl.Window)
    (target : Int32) : IO Unit := do
  let mode ←
    if target == 0 then
      if ← dev.windowSupportsPresentMode window .mailbox then
        pure Sdl.Gpu.PresentMode.mailbox
      else if ← dev.windowSupportsPresentMode window .immediate then
        pure Sdl.Gpu.PresentMode.immediate
      else
        pure Sdl.Gpu.PresentMode.vsync
    else
      pure Sdl.Gpu.PresentMode.vsync
  dev.setSwapchainParameters window .sdr mode

/-- Claim `window` for the shared GPU device and package the GPU renderer as
its `RenderBackend`. Throws when no GPU backend exists (dummy driver). -/
def create (window : Sdl.Window) : IO RenderBackend := do
  let dev ← Gpu.getDevice
  dev.claimWindow window
  let renderer ← Gpu.GpuRenderer.create dev window
  return {
    kind := .gpu
    createTextEngine := Sdl.Ttf.createGpuTextEngine dev
    render := fun clear list mayBlock => renderer.render clear list mayBlock
    coordinatesFromWindow := fun x y => do
      -- Window coordinates → device px (the swapchain is always pixel-sized).
      let scale ← window.pixelDensity
      return (x * scale, y * scale)
    setVSync := fun target => applyVSync dev window target
    sdlRenderer? := none
    dispose := do
      -- Wait for in-flight frames before the swapchain goes away; release
      -- the renderer's pooled textures and buffers deterministically
      -- (pipelines and the sampler fall to their finalizers).
      dev.waitForIdle
      renderer.dispose
      dev.releaseWindow window }

end GpuBackend

end Compose.Draw

end
