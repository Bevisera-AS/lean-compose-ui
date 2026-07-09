import Demos.Desktop

/-!
# Desktop demo entry point (`lake exe demo-desktop`)

A thin `_root_.main` over `Demos.Desktop.desktopApp`, run through
`Compose.application` (multi-window). It lives in its own module so the demo's
content composable stays importable by the MT suite: two exe-root modules each
defining `_root_.main` cannot coexist in one environment, and the test runner
imports every demo's library. See `Demos/Desktop.lean` for the demo itself.
-/

open Compose

/-- Entry point: drive the multi-window application loop
(honors `COMPOSE_MAX_FRAMES` for headless smoke). -/
def main : IO UInt32 :=
  Compose.application Demos.Desktop.desktopApp
