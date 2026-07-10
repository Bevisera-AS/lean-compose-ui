import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier
import Demos.CircleDrawer.Model

/-!
# CircleDrawer behavior tests (`Tests.CircleDrawer`)

End-to-end MT-framework coverage of the M12 CircleDrawer demo: a left-click
creates a circle (probed through the now-enabled Undo button), hover fills the
selection grey (pixel probe), the right-click → "Adjust diameter…" dialog
resizes the circle live and commits one undo step, and undo/redo/branch
invalidation drive the history. The pure history + nearest-circle math is
covered by `#guard`s in `Demos/CircleDrawer/Model.lean`; these tests exercise
the wired UI.
-/

namespace Tests.CircleDrawer
open Compose Compose.Test Tests.Harness
open Demos.CircleDrawer (circleDrawerUi)

/-- A left-click creates a circle (Undo enables); undo empties it (Redo
enables); redo restores it. -/
private def createUndoRedo : IO Unit :=
  runComposeTest circleDrawerUi (width := 520) (height := 480) do
    assertDisabled (.tag "undo")
    assertDisabled (.tag "redo")
    let r ← boundsOf (.tag "canvas")
    clickAt ⟨r.left + 100, r.top + 100⟩
    assertEnabled (.tag "undo")        -- a circle now exists
    assertDisabled (.tag "redo")
    click (.tag "undo")
    assertDisabled (.tag "undo")       -- back to the empty document
    assertEnabled (.tag "redo")
    click (.tag "redo")
    assertEnabled (.tag "undo")        -- circle restored
    assertDisabled (.tag "redo")

/-- A fresh action after an undo invalidates the redo branch. -/
private def newActionClearsRedo : IO Unit :=
  runComposeTest circleDrawerUi (width := 520) (height := 480) do
    let r ← boundsOf (.tag "canvas")
    clickAt ⟨r.left + 60, r.top + 60⟩
    clickAt ⟨r.left + 150, r.top + 150⟩   -- two circles
    click (.tag "undo")                    -- one circle, redo available
    assertEnabled (.tag "redo")
    clickAt ⟨r.left + 220, r.top + 90⟩    -- new creation
    assertDisabled (.tag "redo")           -- redo branch dropped
    assertEnabled (.tag "undo")

/-- Hovering the pointer over a circle fills it grey (the selection). -/
private def hoverFillsSelection : IO Unit :=
  runComposeTest circleDrawerUi (width := 520) (height := 480) do
    let r ← boundsOf (.tag "canvas")
    let cx := r.left + 120
    let cy := r.top + 120
    clickAt ⟨cx, cy⟩
    mouseMove ⟨cx, cy⟩
    awaitIdle
    render
    let c ← pixel cx.toInt32 cy.toInt32
    check s!"hover fills selection grey {showColor c}" (colorNear c 136 136 136 (tol := 30))

/-- Right-click → "Adjust diameter…" opens a dialog whose slider resizes the
circle live; closing commits one undo step that a later undo reverts (a point
inside only the enlarged circle is filled, then bare after undo). -/
private def adjustDiameterFlow : IO Unit :=
  runComposeTest circleDrawerUi (width := 520) (height := 480) do
    let r ← boundsOf (.tag "canvas")
    let cx := r.left + 150
    let cy := r.top + 150
    clickAt ⟨cx, cy⟩                          -- create (diameter 30)
    clickAt ⟨cx, cy⟩ (button := .right)       -- right-click the circle
    assertExists (.text "Adjust diameter…")
    click (.text "Adjust diameter…")           -- open the dialog
    assertExists (.tag "diameter")
    drag (.tag "diameter") ⟨300, 0⟩           -- enlarge toward the max
    click (.tag "done")                        -- commit the adjustment
    assertMissing (.tag "diameter")            -- dialog closed
    -- Enlarged: a point 25 px from the centre is inside → filled on hover.
    mouseMove ⟨cx + 25, cy⟩
    awaitIdle; render
    let c1 ← pixel (cx + 25).toInt32 cy.toInt32
    check s!"enlarged circle filled at +25 {showColor c1}"
      (colorNear c1 136 136 136 (tol := 30))
    -- Undo reverts the diameter (back to 30, radius 15) → +25 now bare.
    click (.tag "undo")
    mouseMove ⟨cx + 25, cy⟩
    awaitIdle; render
    let c2 ← pixel (cx + 25).toInt32 cy.toInt32
    check s!"reverted circle bare at +25 {showColor c2}"
      (!colorNear c2 136 136 136 (tol := 30))
    -- The creation step survives — the adjustment was a distinct undo step.
    assertEnabled (.tag "undo")

/-- Run all CircleDrawer scenarios. -/
def run : IO Unit := do
  scenario "createUndoRedo" createUndoRedo
  scenario "newActionClearsRedo" newActionClearsRedo
  scenario "hoverFillsSelection" hoverFillsSelection
  scenario "adjustDiameterFlow" adjustDiameterFlow

end Tests.CircleDrawer
