import Demos.Crud

/-!
# CRUD demo entry point (`lake exe demo-crud`)

A thin `_root_.main` wrapper over `Demos.Crud.crudUi`. It lives in its own
module (rather than in `Demos/Crud.lean`) so the demo's model + UI stay
importable by the MT suite: two exe-root modules each defining `_root_.main`
cannot coexist in one environment, and the test runner imports both demos'
libraries. See `Demos/Crud.lean` for the demo itself.
-/

open Compose

/-- Entry point. -/
def main : IO UInt32 :=
  runApp "compose crud" 540 420 Demos.Crud.crudUi
    { clearColor := ColorScheme.light.surface }
