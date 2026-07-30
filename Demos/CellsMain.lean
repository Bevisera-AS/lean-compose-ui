import Demos.Cells.Ui

/-!
# `demo-cells` entry point (`Demos/CellsMain.lean`)

A separate root module (outside the `CellsEngine` lib glob) so
`Demos/Cells/Ui.lean` stays importable by the `ComposeTests` MT suite
without colliding with the test runner's `main`.
-/

/-- Entry point. -/
def main : IO UInt32 :=
  Compose.runMaterialApp "7GUIs Cells" 760 520 Demos.Cells.cellsUi
