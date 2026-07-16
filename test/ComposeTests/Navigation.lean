import Compose
import ComposeTests.Harness

/-!
# Navigation test group (`test/ComposeTests/Navigation.lean`)

`BackHandler` (dispatch order, enabled gating, dialog composition, the
unhandled-back quit fallback) and `AnimatedContent` (mid-flight overlap,
settling, entry hygiene under rapid retargeting, per-entry state survival) —
the screen-navigation primitives.
-/

namespace Tests.Navigation
open Compose Compose.Test Tests.Harness

/-- Synthesize the platform back action (`AC_BACK` key-down, as SDL delivers
it when the Android embedder traps the back button). -/
private def pressBack : TestM Unit :=
  sendEvent (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, .acBack, .none, 0, true, false⟩)

/-- Innermost-enabled dispatch: the deepest handler wins, disabling it falls
back outward, removing it likewise; the quit fallback never fires while a
handler consumes. -/
private def backHandlerDispatch : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let innerEnabled ← MutableState.create true
  let innerPresent ← MutableState.create true
  runComposeTest
    (do
      BackHandler (log.modify (·.push "outer"))
      if ← innerPresent.get then
        BackHandler (log.modify (·.push "inner")) (enabled := ← innerEnabled.get))
    (do
      pressBack
      awaitIdle
      checkEq "back: innermost wins" (← log.get) #["inner"]
      liftM (innerEnabled.set false)
      awaitIdle
      pressBack
      awaitIdle
      checkEq "back: disabled falls outward" (← log.get) #["inner", "outer"]
      liftM (innerPresent.set false)
      awaitIdle
      pressBack
      awaitIdle
      checkEq "back: removed falls outward" (← log.get)
        #["inner", "outer", "outer"]
      checkEq "back: handled → no quit" (← (← read).ctx.quitRequested.get) false)

/-- No enabled handler: the shell requests quit (Android: activity finishes
= system back). -/
private def backUnhandledQuits : IO Unit := do
  runComposeTest
    (BackHandler (pure ()) (enabled := false))
    (do
      pressBack
      awaitIdle
      checkEq "back: unhandled requests quit"
        (← (← read).ctx.quitRequested.get) true)

/-- An open dialog consumes back first (dismiss), the screen handler gets the
next one — the Android layering. -/
private def backDismissesDialog : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let dialogOpen ← MutableState.create true
  runComposeTest
    (do
      BackHandler (log.modify (·.push "screen"))
      if ← dialogOpen.get then
        Dialog (onDismissRequest := do
            log.modify (·.push "dismiss")
            dialogOpen.set false)
          (content := Text "modal"))
    (do
      awaitIdle
      pressBack
      awaitIdle
      checkEq "back: dialog dismissed first" (← log.get) #["dismiss"]
      pressBack
      awaitIdle
      checkEq "back: then the screen handler" (← log.get) #["dismiss", "screen"])

/-- Two screens under `AnimatedContent`: both composed mid-flight, only the
target after settling. -/
private def animatedContentSwitch : IO Unit := do
  let screen ← MutableState.create "home"
  runComposeTest
    -- NB the target read must sit inside the composable (an inline `(←
    -- screen.get)` argument would lift into the *test's* IO do-block and
    -- freeze the target).
    (do
      AnimatedContent (← screen.get) fun s =>
        Text s!"screen-{s}" (modifier := Modifier.testTag s!"screen-{s}"))
    (do
      assertExists (.tag "screen-home")
      assertMissing (.tag "screen-game")
      liftM (screen.set "game")
      advanceTimeBy 24
      assertExists (.tag "screen-home")   -- exiting, still composed
      assertExists (.tag "screen-game")   -- entering
      settle
      assertMissing (.tag "screen-home")  -- exit finished → entry dropped
      assertExists (.tag "screen-game"))

/-- Hammer A→B→A mid-flight: the revived entry keeps its identity (remembered
state survives) and no exited entries leak. -/
private def animatedContentRetarget : IO Unit := do
  let screen ← MutableState.create "a"
  let compositions ← IO.mkRef (0 : Nat)
  runComposeTest
    (do
      AnimatedContent (← screen.get) fun s => do
      if s == "a" then
        -- Remembered marker: survives only if the revived entry kept identity.
        let marker ← remember (mutableStateOf 0)
        liftM (m := IO) (compositions.modify (· + 1))
        if (← marker.get) == 0 then liftM (marker.set 1)
        Text "screen-a" (modifier := Modifier.testTag "a")
      else
        Text "screen-b" (modifier := Modifier.testTag "b"))
    (do
      awaitIdle
      liftM (screen.set "b")
      advanceTimeBy 16
      liftM (screen.set "a")   -- reverse mid-exit
      settle
      assertExists (.tag "a")
      assertMissing (.tag "b")
      -- Bounce again and settle on b: a must be gone (no entry leak).
      liftM (screen.set "b")
      settle
      assertMissing (.tag "a")
      assertExists (.tag "b"))

def run : IO Unit := do
  backHandlerDispatch
  backUnhandledQuits
  backDismissesDialog
  animatedContentSwitch
  animatedContentRetarget

end Tests.Navigation
