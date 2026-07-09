import Compose

/-!
# CircleDrawer model + UI (`Demos.CircleDrawer.Model`)

The pure model and composable UI of the 7GUIs CircleDrawer demo, split out
from the `Demos.CircleDrawer` exe root (which only adds `main`) so the MT
behavior tests can import the UI without pulling in a second `_root_.main`.

The 7GUIs *CircleDrawer* task (https://eugenkiss.github.io/7guis/tasks):
Undo/Redo buttons above a framed canvas. Left-click on empty canvas draws an
unfilled circle of a fixed default diameter centred at the click. The circle
under the pointer whose disc contains it — nearest centre wins — is the
selection, drawn filled grey. Right-click on the selected circle opens a
popup menu with "Adjust diameter…", which opens a modal `Dialog` whose
`Slider` resizes the circle *live*. Closing the dialog commits one undo step
(intermediate slider values are not separate steps); undo/redo walk the
history and a fresh action after undo invalidates redo.

The state is a pure `Array Circle` inside an undo/redo `History` zipper with
pure operations (see the `#guard`s below). The canvas combines
`detectTapGestures` (`onTap` creates, `onSecondaryTap` opens the context
menu) with `detectHover` for live selection. Headless:
`SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-circles`.
-/

namespace Demos.CircleDrawer
open Compose
open Compose.Draw

/-! ## Pure model -/

/-- Default diameter (px) of a freshly drawn circle. -/
def defaultDiameter : Float32 := 30

/-- One drawn circle: its `center` (canvas-local px) and `diameter` (px).
Pure data, no rendering concerns. -/
structure Circle where
  center : Offset
  diameter : Float32 := defaultDiameter
  deriving Repr, BEq, Inhabited

namespace Circle

/-- Half the diameter. -/
def radius (c : Circle) : Float32 := c.diameter / 2

/-- Whether `p` lies within the disc (boundary inclusive). -/
def contains (c : Circle) (p : Offset) : Bool := c.center.distance p ≤ c.radius

end Circle

#guard (Circle.mk ⟨50, 50⟩ 30).contains ⟨50, 50⟩          -- centre
#guard (Circle.mk ⟨50, 50⟩ 30).contains ⟨50, 65⟩          -- on boundary (r = 15)
#guard !(Circle.mk ⟨50, 50⟩ 30).contains ⟨50, 71⟩         -- 21 > 15

/-- Set circle `i`'s diameter (no-op if out of range). Backs both the live
adjust preview and the committed adjustment. -/
def adjustDiameter (cs : Array Circle) (i : Nat) (d : Float32) : Array Circle :=
  cs.modify i (fun c => { c with diameter := d })

/-- The selected circle: among circles whose disc contains `p`, the one whose
centre is nearest `p`; `none` if `p` is inside no circle. Mirrors the 7GUIs
hover rule (nearest centre wins). -/
def selectedIndex (cs : Array Circle) (p : Offset) : Option Nat := Id.run do
  let mut best : Option (Nat × Float32) := none
  for i in [0:cs.size] do
    let c := cs[i]!
    if c.contains p then
      let d := c.center.distanceSquared p
      if best.all (fun bt => d < bt.2) then
        best := some (i, d)
  return best.map (·.1)

#guard selectedIndex #[⟨⟨30, 30⟩, 30⟩, ⟨⟨100, 100⟩, 30⟩] ⟨30, 30⟩ == some 0
#guard selectedIndex #[⟨⟨30, 30⟩, 30⟩, ⟨⟨100, 100⟩, 30⟩] ⟨100, 100⟩ == some 1
#guard selectedIndex #[⟨⟨30, 30⟩, 30⟩, ⟨⟨100, 100⟩, 30⟩] ⟨200, 200⟩ == none
-- Overlapping discs: the nearer centre wins (48 is 8 from 40, 7 from 55).
#guard selectedIndex #[⟨⟨40, 40⟩, 40⟩, ⟨⟨55, 40⟩, 40⟩] ⟨48, 40⟩ == some 1

/-- Undo/redo history over the circle document: the `current` snapshot, the
`past` snapshots (most recent first) reachable by undo, and the `future`
snapshots reachable by redo. A committed action (a creation or a *completed*
diameter adjustment) pushes `current` onto `past` and clears `future`; live
slider movements never commit, so one adjustment is one undo step. -/
structure History where
  current : Array Circle := #[]
  past : List (Array Circle) := []
  future : List (Array Circle) := []
  deriving Repr, BEq, Inhabited

namespace History

/-- The empty document. -/
def empty : History := {}

/-- Is there an undo step available? -/
def canUndo (h : History) : Bool := !h.past.isEmpty

/-- Is there a redo step available? -/
def canRedo (h : History) : Bool := !h.future.isEmpty

/-- Commit `next` as the new document, recording one undo step and dropping
any redo branch. -/
def commit (h : History) (next : Array Circle) : History :=
  { current := next, past := h.current :: h.past, future := [] }

/-- Create a circle of diameter `d` centred at `p` (a committed action). -/
def addCircle (h : History) (p : Offset) (d : Float32 := defaultDiameter) : History :=
  h.commit (h.current.push { center := p, diameter := d })

/-- Step back one committed action. No-op when there is nothing to undo. -/
def undo (h : History) : History :=
  match h.past with
  | [] => h
  | prev :: rest => { current := prev, past := rest, future := h.current :: h.future }

/-- Step forward one undone action. No-op when there is nothing to redo. -/
def redo (h : History) : History :=
  match h.future with
  | [] => h
  | next :: rest => { current := next, past := h.current :: h.past, future := rest }

end History

#guard !History.empty.canUndo && !History.empty.canRedo
#guard (History.empty.addCircle ⟨10, 10⟩).current.size == 1
#guard (History.empty.addCircle ⟨10, 10⟩).canUndo
-- undo removes the created circle; redo restores it
#guard ((History.empty.addCircle ⟨10, 10⟩).undo).current.size == 0
#guard (((History.empty.addCircle ⟨10, 10⟩).undo).redo).current.size == 1
-- a completed adjustment is one undo step; undo reverts the diameter
#guard
  let h0 := History.empty.addCircle ⟨50, 50⟩          -- d = 30
  let h1 := h0.commit (adjustDiameter h0.current 0 60)
  h1.current[0]!.diameter == 60 && h1.undo.current[0]!.diameter == 30
-- a fresh action after undo invalidates the redo branch
#guard
  let h := (History.empty.addCircle ⟨0, 0⟩).addCircle ⟨1, 1⟩  -- 2 circles, 2 steps
  let h' := h.undo.addCircle ⟨2, 2⟩                            -- undo → 1, then create
  !h'.canRedo && h'.current.size == 2

/-! ## UI -/

/-- The CircleDrawer screen (see the module docstring). -/
composable def circleDrawerUi : Composable Unit := do
  let history   ← remember (mutableStateOf History.empty)
  let hoverPos  ← remember (mutableStateOf (none : Option Offset))
  let menuAt    ← remember (mutableStateOf (none : Option (Nat × Offset)))
  let dialogFor ← remember (mutableStateOf (none : Option Nat))
  let liveDiam  ← remember (mutableStateOf defaultDiameter)
  let canvasRect ← remember (mutableStateOf Rect.zero)

  -- Pointer callbacks touch only stable refs — the gesture coroutines launch
  -- once (constant keys), so they must not capture per-frame values.
  let onLeft  := fun (p : Offset) => history.modify (·.addCircle p)
  let onHover := fun (p : Offset) => hoverPos.set (some p)
  let onRight := fun (p : Offset) => do
    let h ← history.get
    if let some idx := selectedIndex h.current p then
      hoverPos.set (some p)
      menuAt.set (some (idx, p))

  -- Close the adjust dialog, committing one undo step iff the diameter moved.
  let closeDialog : IO Unit := do
    if let some idx := (← dialogFor.get) then
      let h ← history.get
      let d ← liveDiam.get
      let orig := (h.current[idx]?.map (·.diameter)).getD d
      if orig != d then history.set (h.commit (adjustDiameter h.current idx d))
      dialogFor.set none

  let h    ← history.get
  let dlg  ← dialogFor.get
  let live ← liveDiam.get
  let hp   ← hoverPos.get
  -- The displayed document folds in the live adjust preview, if any.
  let display := match dlg with
    | some idx => adjustDiameter h.current idx live
    | none     => h.current
  let sel := hp.bind (selectedIndex display)

  MaterialTheme (content := do
    let colors ← MaterialTheme.colorScheme
    let canvasDraw : DrawM Unit := do
      for i in [0:display.size] do
        let c := display[i]!
        if sel == some i then
          DrawScope.drawCircle (.solid Color.gray) c.center c.radius (style := .fill)
        DrawScope.drawCircle (.solid colors.onSurface) c.center c.radius (style := .stroke 1.5)
    Column (Modifier.padding (all := 16)) (verticalArrangement := .spacedBy 12)
        (horizontalAlignment := .centerHorizontally) (content := fun _ => do
      Text "CircleDrawer" (style := { fontSize := 22 })
      Row {} (horizontalArrangement := .spacedBy 8) (content := fun _ => do
        Button (history.modify (·.undo)) (enabled := h.canUndo)
          (modifier := Modifier.testTag "undo") (content := Text "Undo")
        Button (history.modify (·.redo)) (enabled := h.canRedo)
          (modifier := Modifier.testTag "redo") (content := Text "Redo"))
      Box (Modifier.fillMaxWidth |>.height 360
            |>.background colors.surface
            |>.border 1 colors.outlineVariant
            |>.onGloballyPositioned canvasRect.set
            |>.drawBehind canvasDraw
            |>.pointerInput 0 (detectTapGestures
                (onTap := some onLeft) (onSecondaryTap := some onRight))
            |>.pointerInput 1 (detectHover
                (onEnter := onHover) (onMove := onHover))
            |>.testTag "canvas")
        (content := fun _ => pure ())
      -- Right-click context menu, anchored at the click (window coords).
      match (← menuAt.get) with
      | none => pure ()
      | some (idx, p) =>
        let r ← canvasRect.get
        DropdownMenu (expanded := true) (onDismissRequest := menuAt.set none)
          (offset := ⟨(r.left + p.x).floor.toInt32, (r.top + p.y).floor.toInt32⟩)
          (content :=
            DropdownMenuItem "Adjust diameter…" (onClick := do
              let h ← history.get
              dialogFor.set (some idx)
              liveDiam.set ((h.current[idx]?.map (·.diameter)).getD defaultDiameter)
              menuAt.set none))
      -- The live diameter-adjust dialog.
      match dlg with
      | none => pure ()
      | some idx =>
        let center := (h.current[idx]?.map (·.center)).getD .zero
        Dialog (onDismissRequest := closeDialog) (content :=
          Surface (Modifier.width 320) (shape := .rounded 16) (content :=
            Column (Modifier.padding (all := 20)) (verticalArrangement := .spacedBy 16)
                (content := fun _ => do
              Text s!"Adjust diameter of circle at ({center.x.toUInt32}, {center.y.toUInt32})"
              Slider live liveDiam.set (valueRange := (4, 160))
                (modifier := Modifier.fillMaxWidth |>.testTag "diameter")
              Row (Modifier.fillMaxWidth) (horizontalArrangement := Arrangement.«end») (content := fun _ =>
                TextButton closeDialog (modifier := Modifier.testTag "done")
                  (content := Text "Done")))))))

end Demos.CircleDrawer
