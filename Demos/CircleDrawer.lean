import Demos.CircleDrawer.Model

/-!
# CircleDrawer demo (`lake exe demo-circles`)

The 7GUIs *CircleDrawer* task: Undo/Redo over a circle canvas, a right-click
popup menu, and a live diameter-adjust dialog. The model and UI live in
`Demos.CircleDrawer.Model` (imported here and by the MT tests); this module is
just the executable entry point. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-circles`.
-/

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runApp "compose circles" 520 480 Demos.CircleDrawer.circleDrawerUi
    { clearColor := Compose.ColorScheme.light.background }
