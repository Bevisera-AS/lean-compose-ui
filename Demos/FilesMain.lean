import Demos.Files

/-!
# File manager entry point (`lake exe demo-files`)

A thin `_root_.main` over `Demos.Files.filesApp`, run through
`Compose.runMaterialApp`.
It lives in its own module so the demo's content composables stay importable by
the MT suite: two exe-root modules each defining `_root_.main` cannot coexist in
one environment, and the test runner imports every demo's library. See
`Demos/Files.lean` for the demo itself. Headless smoke:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-files`.
-/

open Compose

/-- Entry point: open the 640×480 file-manager window at `$HOME`
(honors `COMPOSE_MAX_FRAMES` for headless smoke). -/
def main : IO UInt32 :=
  runMaterialApp "Files" 640 480 Demos.Files.filesApp
