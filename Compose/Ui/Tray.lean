import Sdl
import Compose.Runtime.Effects
import Compose.Runtime.Macro
import Compose.Ui.Window

namespace Compose

/-!
# Declarative system tray (`Compose/Ui/Tray.lean`)

An OS system-tray icon managed declaratively, mirroring Compose Desktop's
`androidx.compose.ui.window.Tray`. You describe the menu as a pure `Array
TrayItem` spec; the `Tray` composable owns the SDL tray handle — creating it on
first composition, reconciling it when the spec changes, and destroying it on
dispose. Composing two `Tray`s yields two OS icons; each effect owns its handle.

Layer note: this component imports `Sdl`, so it lives in `Compose/Ui/`, not
`Compose/Material/`.

## Reconciliation model

The spec carries `IO Unit` callbacks, which are **not comparable**. To keep the
"did anything change?" decision pure and unit-testable, every applicable change
is projected onto a comparable `TraySnapshot` (menu *shape* + tooltip + whether
an icon is present). `reconcilePlan` diffs two snapshots into a `TrayReconcile`.
Consequences, each deliberate:

* **Menu** — a shape change (labels / enabled / checked / separators / submenu
  structure) rebuilds the whole menu (clear + re-insert). Diffing entry-by-entry
  buys little over a rebuild and is far more error-prone, so we don't.
* **Callbacks** — always freshly bound during a rebuild, never cached or
  compared. A callback whose *behaviour* changes without any shape change is
  therefore only re-bound on the next shape change. In practice callbacks close
  over stable `MutableState` handles, so this is rarely observable; when it
  matters, force a rebuild (change the spec) or remount via `key`.
* **Tooltip** — a plain `Option String`, compared directly.
* **Icon** — `Sdl.Surface` is an opaque, non-comparable handle, so only its
  *presence* (`some`/`none`) is tracked: setting an icon from none, or clearing
  it, is applied; swapping one surface for another is not detected (remount via
  `key`, or change the tooltip/menu to force a full apply).

Callbacks fire on the main thread during SDL event pumping (SDL pumps them from
its own event loop, so the app loop needs no changes), so writing Compose state
from a tray callback is safe and schedules a frame like any other state write.
-/

/-- One entry in a tray menu — the pure, declarative spec. Mirrors the menu
model behind `androidx.compose.ui.window.Tray`.

* `item` — a clickable entry. `checked := some b` makes it a checkbox showing
  state `b`; `none` (the default) is a plain button.
* `separator` — a horizontal divider.
* `submenu` — a labelled entry opening a nested menu. -/
inductive TrayItem where
  /-- A clickable button (`checked := none`) or checkbox (`checked := some b`).
  `onClick` fires on the main thread when selected. -/
  | item (label : String) (onClick : IO Unit)
      (enabled : Bool := true) (checked : Option Bool := none)
  /-- A horizontal separator. -/
  | separator
  /-- A labelled submenu holding nested items. -/
  | submenu (label : String) (items : Array TrayItem)

/-! ## Pure reconciliation core (unit-testable, SDL-free) -/

/-- The comparable projection of a `TrayItem`: everything that drives the SDL
menu *except* the non-comparable `IO Unit` callback. Two items with the same
shape are considered structurally identical for reconciliation. -/
inductive TrayShape where
  /-- Projection of `TrayItem.item` (callback dropped). -/
  | item (label : String) (enabled : Bool) (checked : Option Bool)
  /-- Projection of `TrayItem.separator`. -/
  | separator
  /-- Projection of `TrayItem.submenu`. -/
  | submenu (label : String) (items : Array TrayShape)
  deriving BEq, Inhabited

/-- Project a `TrayItem` onto its comparable `TrayShape`. -/
partial def TrayItem.shape : TrayItem → TrayShape
  | .item label _ enabled checked => .item label enabled checked
  | .separator => .separator
  | .submenu label items => .submenu label (items.map TrayItem.shape)

/-- Project a menu spec onto its comparable shape list. -/
def TrayItem.shapes (items : Array TrayItem) : Array TrayShape :=
  items.map TrayItem.shape

/-- The comparable fingerprint of a whole tray spec: menu shape, tooltip, and
whether an icon is present (see the module docstring on why the icon surface
itself is not compared). -/
structure TraySnapshot where
  /-- Comparable projection of the menu. -/
  shapes : Array TrayShape
  /-- The tooltip text, if any. -/
  tooltip : Option String
  /-- Whether an icon surface is attached (presence only). -/
  hasIcon : Bool
  deriving BEq, Inhabited

/-- Build a `TraySnapshot` from a full spec. -/
def TraySnapshot.of (menu : Array TrayItem) (hasIcon : Bool)
    (tooltip : Option String) : TraySnapshot :=
  { shapes := TrayItem.shapes menu, tooltip, hasIcon }

/-- The set of SDL operations a recomposition must apply, decided purely by
diffing two `TraySnapshot`s. Each flag maps to one reconcile step. -/
structure TrayReconcile where
  /-- Icon presence changed (set the new icon, or clear it). -/
  applyIcon : Bool
  /-- Tooltip text changed. -/
  applyTooltip : Bool
  /-- Menu shape changed: rebuild all entries (and re-bind callbacks). -/
  rebuildMenu : Bool
  deriving BEq, Repr, Inhabited

/-- Pure reconciliation decision: what changed between the applied snapshot
`old` and the desired snapshot `new`. Unit-testable without SDL. -/
def reconcilePlan (old new : TraySnapshot) : TrayReconcile where
  applyIcon := old.hasIcon != new.hasIcon
  applyTooltip := old.tooltip != new.tooltip
  rebuildMenu := old.shapes != new.shapes

/-- Whether a plan requires no SDL work (snapshots are equivalent). -/
def TrayReconcile.isNoop (p : TrayReconcile) : Bool :=
  !p.applyIcon && !p.applyTooltip && !p.rebuildMenu

-- Pure reconciliation checks (compile-time). Snapshots are built with
-- `TrayShape` literals directly, so these stay kernel-reducible (the
-- `TrayItem → TrayShape` projection is exercised by the runtime test group).
section
/-- A snapshot from an explicit shape list (test helper). -/
private def snap (shapes : Array TrayShape) (hasIcon : Bool := false)
    (tooltip : Option String := none) : TraySnapshot :=
  { shapes, tooltip, hasIcon }

-- Equal specs reconcile to a no-op.
#guard (reconcilePlan (snap #[.item "A" true none, .separator] true (some "t"))
                      (snap #[.item "A" true none, .separator] true (some "t"))).isNoop

-- A label change forces a menu rebuild but nothing else.
#guard reconcilePlan (snap #[.item "A" true none]) (snap #[.item "B" true none])
       == { applyIcon := false, applyTooltip := false, rebuildMenu := true }

-- A callback-only change is invisible to the plan (the projection dropped the
-- callback, so both sides share the same shape).
#guard (reconcilePlan (snap #[.item "A" true none]) (snap #[.item "A" true none])).isNoop

-- A checked-state change is a shape change → rebuild.
#guard (reconcilePlan (snap #[.item "A" true (some false)])
                      (snap #[.item "A" true (some true)])).rebuildMenu

-- Toggling a checkbox into a plain button is a shape change.
#guard (reconcilePlan (snap #[.item "A" true (some false)])
                      (snap #[.item "A" true none])).rebuildMenu

-- An `enabled` change is a shape change → rebuild.
#guard (reconcilePlan (snap #[.item "A" true none])
                      (snap #[.item "A" false none])).rebuildMenu

-- A submenu's nested change bubbles up to a rebuild.
#guard (reconcilePlan (snap #[.submenu "M" #[.item "A" true none]])
                      (snap #[.submenu "M" #[.item "B" true none]])).rebuildMenu

-- A tooltip-only change applies just the tooltip.
#guard reconcilePlan (snap #[] false (some "old")) (snap #[] false (some "new"))
       == { applyIcon := false, applyTooltip := true, rebuildMenu := false }

-- Attaching an icon (none → some) applies just the icon.
#guard reconcilePlan (snap #[] false none) (snap #[] true none)
       == { applyIcon := true, applyTooltip := false, rebuildMenu := false }

-- Independent changes compose into independent flags.
#guard reconcilePlan (snap #[.item "A" true none] false (some "t"))
                     (snap #[.item "B" true none] true none)
       == { applyIcon := true, applyTooltip := true, rebuildMenu := true }

end

/-! ## SDL menu building (main-thread, guarded by the composable below) -/

/-- Insert one `TrayItem` (and, for submenus, its children recursively) at the
end of `menu`, binding the fresh callback. Main-thread only. -/
partial def insertTrayItem (menu : Sdl.TrayMenu) : TrayItem → IO Unit
  | .separator => do
    let _ ← menu.insertEntryAt (-1) none .button
  | .item label onClick enabled checked => do
    let kind : Sdl.TrayEntryFlags := match checked with
      | some _ => .checkbox
      | none => .button
    let withChecked := if checked == some true then kind ||| .checked else kind
    let flags := if enabled then withChecked else withChecked ||| .disabled
    let entry ← menu.insertEntryAt (-1) (some label) flags
    -- Bind fresh on every build; never cached or compared (see module docs).
    entry.setCallback (some onClick)
  | .submenu label items => do
    let entry ← menu.insertEntryAt (-1) (some label) .submenu
    let sub ← entry.createSubmenu
    for it in items do
      insertTrayItem sub it

/-- Clear every entry of `menu` (removing back-to-front). Main-thread only. -/
def clearTrayMenu (menu : Sdl.TrayMenu) : IO Unit := do
  let entries ← menu.getEntries
  for entry in entries.reverse do
    entry.remove

/-- Rebuild `menu` from scratch to match `items`: clear, then re-insert. Simpler
and less error-prone than entry diffing (see the module docstring). -/
def buildTrayMenu (menu : Sdl.TrayMenu) (items : Array TrayItem) : IO Unit := do
  clearTrayMenu menu
  for it in items do
    insertTrayItem menu it

/-- The live handle backing a mounted `Tray`: the SDL tray, its top-level menu,
and the last-applied snapshot driving `reconcilePlan`. -/
structure TrayState where
  /-- The owned SDL tray root. -/
  tray : Sdl.Tray
  /-- Its top-level menu. -/
  menu : Sdl.TrayMenu
  /-- The snapshot currently reflected in the OS tray. -/
  snapshot : TraySnapshot

instance : Nonempty TrayState :=
  ⟨{ tray := Classical.choice inferInstance
     menu := Classical.choice inferInstance
     snapshot := default }⟩

/-- Apply `plan` to a live tray, given the desired spec. Returns the new state
with an updated snapshot. Factored out (and pure in its *decision*, via `plan`)
so the reconcile path is observable in tests. Main-thread only. -/
def applyReconcile (st : TrayState) (plan : TrayReconcile) (menu : Array TrayItem)
    (icon : Option Sdl.Surface) (tooltip : Option String) : IO TrayState := do
  if plan.applyIcon then st.tray.setIcon icon
  if plan.applyTooltip then st.tray.setTooltip tooltip
  if plan.rebuildMenu then buildTrayMenu st.menu menu
  return { st with snapshot := TraySnapshot.of menu icon.isSome tooltip }

/-- Reconcile a (possibly absent) live tray toward the desired spec. When the
handle is `none` — creation failed, e.g. headless — this is a no-op. Uses
`reconcilePlan` for the pure decision, then `applyReconcile` for the effect.
Main-thread only. -/
def reconcileTray (stateRef : IO.Ref (Option TrayState)) (menu : Array TrayItem)
    (icon : Option Sdl.Surface) (tooltip : Option String) : IO Unit := do
  match ← stateRef.get with
  | none => pure ()
  | some st =>
    let plan := reconcilePlan st.snapshot (TraySnapshot.of menu icon.isSome tooltip)
    if plan.isNoop then
      pure ()
    else
      stateRef.set (some (← applyReconcile st plan menu icon tooltip))

/-- Create the SDL tray and build its initial menu, returning the live state.
Throws if `createTray` fails; the caller guards this for headless environments.
Main-thread only. -/
def mountTray (menu : Array TrayItem) (icon : Option Sdl.Surface)
    (tooltip : Option String) : IO TrayState := do
  let tray ← Sdl.createTray icon tooltip
  let m ← tray.createMenu
  buildTrayMenu m menu
  return { tray, menu := m, snapshot := TraySnapshot.of menu icon.isSome tooltip }

/-- A declarative OS system-tray icon. Mirrors
`androidx.compose.ui.window.Tray`.

Creates the tray on first composition, reconciles it when `menu`/`icon`/`tooltip`
change (see the module docstring for the exact semantics), and destroys it on
dispose. Composing two `Tray`s yields two independent OS icons.

Tray creation can fail (an unsupported platform, or a headless CI driver); such
a failure is swallowed and the tray is simply absent — the composable never
throws and reconciliation quietly no-ops. -/
def Tray (menu : Array TrayItem) (icon : Option Sdl.Surface := none)
    (tooltip : Option String := none) : Composable Unit := do
  let stateRef ← remember (IO.mkRef (none : Option TrayState))
  -- Own the OS handle: create on enter (guarded), destroy on leave.
  DisposableEffect () do
    let st? ← (try
        pure (some (← mountTray menu icon tooltip))
      catch _ =>
        pure none)
    stateRef.set st?
    pure do
      if let some st ← stateRef.get then
        try st.tray.destroy catch _ => pure ()
      stateRef.set none
  -- Reconcile after every applied composition this call takes part in. Runs
  -- after the create effect above on first composition, so it starts as a
  -- no-op and only does work once the spec actually changes.
  SideEffect (reconcileTray stateRef menu icon tooltip)

end Compose
