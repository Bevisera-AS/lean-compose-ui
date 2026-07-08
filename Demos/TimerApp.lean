import Demos.Timer

/-!
# Timer demo entry point (`lake exe demo-timer`)

A thin `_root_.main` wrapper over `Demos.Timer.timerUi`. It lives in its own
module (rather than in `Demos/Timer.lean`) so the demo's model + UI stay
importable by the MT suite: two exe-root modules each defining `_root_.main`
cannot coexist in one environment, and the test runner imports both demos'
libraries. See `Demos/Timer.lean` for the demo itself.
-/

open Compose

/-- Entry point. -/
def main : IO UInt32 :=
  runApp "compose timer" 420 320 Demos.Timer.timerUi
    { clearColor := ColorScheme.light.surface }
