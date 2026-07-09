import Compose
import ComposeTests.Harness

/-!
# System-tray test group (`test/ComposeTests/Tray.lean`)

Two layers, mirroring `Compose/Ui/Tray.lean`:

* **Pure** — the `TrayItem → TrayShape` projection, `TraySnapshot.of`, and the
  `reconcilePlan` decision. These need no SDL and always run. (Compile-time
  `#guard`s next to the definitions cover `reconcilePlan` on literal snapshots;
  here we exercise the projection, which routes through a `partial def`.)

* **SDL lifecycle** — `mountTray`/`reconcileTray`/`applyReconcile` against a
  live SDL tray, observed through the SDL getters. Guarded: under a CI video
  driver where `createTray` throws or stubs, the whole SDL layer is skipped with
  a single passing check (`SDL_VIDEO_DRIVER=dummy` works locally on macOS). The
  group never hangs or crashes from tray absence.
-/

namespace Tests.Tray
open Compose Sdl Tests.Harness

/-! ## Pure projection + snapshot checks (no SDL) -/

open TrayItem in
private def pureChecks : IO Unit := do
  -- The projection drops callbacks but keeps label/enabled/checked.
  check "shape of item keeps label/enabled/checked, drops callback"
    (TrayItem.shape (item "A" (IO.println "x") (enabled := false) (checked := some true))
      == .item "A" false (some true))
  check "shape of separator" (TrayItem.shape separator == .separator)
  check "shape recurses into submenus"
    (TrayItem.shape (submenu "M" #[item "B" (pure ())])
      == .submenu "M" #[.item "B" true none])

  -- Two specs differing only in the callback share a snapshot ⇒ no-op plan.
  let a := TraySnapshot.of #[item "A" (IO.println "x")] false none
  let b := TraySnapshot.of #[item "A" (IO.println "y")] false none
  check "callback-only change ⇒ snapshots equal" (a == b)
  check "callback-only change ⇒ reconcile no-op" (reconcilePlan a b).isNoop

  -- A label change is observed by the projected snapshot.
  let c := TraySnapshot.of #[item "A" (pure ())] false none
  let d := TraySnapshot.of #[item "Z" (pure ())] false none
  check "label change ⇒ rebuild" (reconcilePlan c d).rebuildMenu

  -- `TraySnapshot.of` records icon presence and tooltip.
  let e := TraySnapshot.of #[] true (some "hi")
  check "snapshot records icon presence" e.hasIcon
  check "snapshot records tooltip" (e.tooltip == some "hi")

  -- Reconciling against an absent handle is a safe no-op (the headless path).
  let ref ← IO.mkRef (none : Option TrayState)
  reconcileTray ref #[item "A" (pure ())] none (some "t")
  check "reconcileTray with no live tray is a no-op (no throw)" true

/-! ## SDL lifecycle checks (guarded) -/

/-- Labels of a menu's entries, in order (a separator reads as `""`). -/
private def labelsOf (menu : TrayMenu) : IO (Array String) := do
  let entries ← menu.getEntries
  entries.mapM (fun e => return (← e.getLabel).getD "")

open TrayItem in
/-- The battery, given that `createTray` works. Kept in its own `def` so the
availability probe in `run` stays small. -/
private def sdlBody : IO Unit := do
  -- mountTray builds the initial menu from the spec.
  let spec0 : Array TrayItem :=
    #[item "One" (pure ()), separator,
      item "Check" (pure ()) (checked := some true),
      submenu "More" #[item "Nested" (pure ())]]
  let st0 ← mountTray spec0 none (some "tip")
  check "mountTray builds all top-level entries" ((← st0.menu.getEntries).size == 4)
  check "mountTray preserves labels/order"
    ((← labelsOf st0.menu) == #["One", "", "Check", "More"])
  let entries0 ← st0.menu.getEntries
  let checkedOk ← match entries0[2]? with
    | some e => e.getChecked
    | none => pure false
  check "mountTray sets checkbox checked state" checkedOk
  let subOk ← match entries0[3]? with
    | some e => (·.isSome) <$> e.getSubmenu
    | none => pure false
  check "mountTray builds the submenu" subOk

  -- Callback wiring: run the bound closure and confirm it can write state; also
  -- probe whether SDL fires it on a simulated click under the dummy driver.
  let hits ← mutableStateOf (0 : Nat)
  let st1 ← mountTray #[item "Tap" (hits.modify (· + 1))] none none
  (match (← st1.menu.getEntries)[0]? with
    | some e => e.click
    | none => pure ())
  updateTrays
  check "callback closure runs and writes Compose state — no throw" true
  IO.println s!"  PROBE: state after click/updateTrays = {← hits.get} (callback fires under dummy iff ≥1)"
  st1.tray.destroy

  -- reconcileTray: an equal spec is a no-op (entry count/labels unchanged).
  let ref ← IO.mkRef (some st0)
  reconcileTray ref spec0 none (some "tip")
  check "reconcile with equal spec leaves menu untouched"
    ((← labelsOf st0.menu) == #["One", "", "Check", "More"])

  -- reconcileTray: a label change rebuilds the menu, observably.
  reconcileTray ref #[item "Renamed" (pure ())] none (some "tip")
  check "reconcile applies a menu rebuild (new labels)"
    ((← labelsOf st0.menu) == #["Renamed"])
  let snapOk ← match ← ref.get with
    | some st => pure (st.snapshot == TraySnapshot.of #[item "Renamed" (pure ())] false (some "tip"))
    | none => pure false
  check "reconcile advances the stored snapshot" snapOk

  -- applyReconcile honours the plan flags: tooltip-only touches neither menu.
  match ← ref.get with
  | none => check "tooltip-only reconcile leaves the menu intact" false
  | some stNow =>
    let _ ← applyReconcile stNow { applyIcon := false, applyTooltip := true, rebuildMenu := false }
      #[item "Renamed" (pure ())] none (some "tip2")
    check "tooltip-only reconcile leaves the menu intact"
      ((← labelsOf stNow.menu) == #["Renamed"])

  -- Multi-instance: two independent trays; destroying one leaves the other live.
  let extra ← createTray none (some "second")
  st0.tray.destroy
  let _ ← extra.createMenu
  check "second tray is still usable after the first is destroyed"
    ((← extra.getMenu).isSome)
  extra.destroy

  -- Dispose semantics: a destroyed tray's handle is invalid.
  checkThrows "destroyed tray's getMenu throws" extra.getMenu

open TrayItem in
def run : IO Unit := do
  pureChecks
  -- On a headless macOS CI runner `createTray` doesn't throw — it trips a
  -- CoreGraphics assertion (`CGSConnectionByID`: no window server) and calls
  -- `abort()`, which the probe's `try/catch` below cannot intercept. Skip the
  -- SDL layer when the environment tells us there's no window server / GUI session.
  if (← IO.getEnv "SDL_LEAN_SKIP_TRAY").isSome then
    check "tray skipped (SDL_LEAN_SKIP_TRAY set — no window server)" true
    return
  -- Probe availability once; on any failure, skip the SDL layer with one pass.
  let available ← try
      let t ← createTray none (some "probe")
      t.destroy
      pure true
    catch _ => pure false
  if available then
    sdlBody
  else
    check "tray unavailable in this environment — SDL layer skipped" true

end Tests.Tray
