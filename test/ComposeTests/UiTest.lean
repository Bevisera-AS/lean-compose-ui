import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# UiTest group (`test/ComposeTests/UiTest.lean`)

MT's self-test suite: the framework proving itself on known trees. Covers
finders (hit/miss/multi + the semantics dump in failure messages), actions
flowing through the **real** input pipeline (a click toggles a `Checkbox`
via its true hit path; keys route through focus; text enters through the IME
commit path; drags drive a `Slider`; wheels drive `verticalScroll`), overlay
content (dialog, dropdown menu) appearing in the semantics tree, and the
controlled clock driving an animation deterministically.
-/

namespace Tests.UiTest
open Compose Compose.Test Tests.Harness

/-- Expect `body` to fail, and its message to contain every needle (the way
tests assert that failures carry the semantics dump). -/
private def failsWith (label : String) (needles : List String)
    (body : TestM Unit) : TestM Unit := do
  let msg? ← try
      body
      pure (none : Option String)
    catch e =>
      pure (some (toString e))
  match msg? with
  | none => throw (IO.userError s!"{label}: expected a failure, got success")
  | some msg =>
    for nd in needles do
      unless (msg.splitOn nd).length > 1 do
        throw (IO.userError s!"{label}: message lacks \"{nd}\"\n--- message ---\n{msg}")
    IO.println s!"ok {label}"

/-- Width of a rect (bounds assertions). -/
private def rw (r : Compose.Rect) : Float32 := r.right - r.left

/-! ## Finders, merging, failure dumps -/

private def findersAndFailures : IO Unit := runComposeTest
  (content := Column {} (content := fun _ => do
    Text "alpha"
    Text "dup"
    Text "dup"
    Button (pure ()) (modifier := Modifier.testTag "go-btn") (content := Text "go")
    Button (pure ()) (enabled := false) (modifier := Modifier.testTag "no-btn")
      (content := Text "nope")))
  do
    assertExists (.text "alpha")
    assertMissing (.text "gamma")
    assertCountEquals (.text "dup") 2
    -- Merging: the button node itself carries its label text …
    assertExists ((Matcher.text "go").and (.role .button))
    assertExists (.tag "go-btn")
    assertEnabled (.tag "go-btn")
    assertDisabled (.tag "no-btn")
    -- … but in the unmerged tree, text and role live on different nodes.
    assertCountEquals ((Matcher.text "go").and (.role .button)) 0 (unmerged := true)
    assertCountEquals (.role .button) 2 (unmerged := true)
    -- Failures are precise and carry the tree dump.
    failsWith "find: ambiguity reported with the dump"
      ["found 2", "texts=[\"dup\"]"] (do let _ ← find (.text "dup"))
    failsWith "find: no match reported with the dump"
      ["found 0", "semantics tree:", "role=button"] (do let _ ← find (.text "gamma"))
    failsWith "assertExists: failure carries the dump"
      ["no matching node", "tag=\"go-btn\""] (assertExists (.text "gamma"))
    failsWith "assertTextEquals: mismatch shows the node"
      ["expected \"nope\"", "texts=[\"go\"]"] (assertTextEquals (.tag "go-btn") "nope")

/-! ## Clicks through the real router -/

private def clickThroughRouter : IO Unit := do
  let checked ← mutableStateOf false
  let offCalls ← IO.mkRef (0 : Nat)
  let count ← mutableStateOf (0 : Nat)
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      Checkbox (← checked.get) checked.set (modifier := Modifier.testTag "cb")
      Checkbox false (fun _ => offCalls.modify (· + 1)) (enabled := false)
        (modifier := Modifier.testTag "cb-off")
      Button (count.modify (· + 1)) (content := Text "+1")
      Text s!"count: {← count.get}"))
    do
      assertUnchecked (.tag "cb")
      -- The click is a synthesized SDL press+release hitting the checkbox's
      -- real bounds — toggling proves hit test, capture, and tap detection.
      click (.tag "cb")
      assertChecked (.tag "cb")
      click (.tag "cb")
      assertUnchecked (.tag "cb")
      -- A disabled checkbox swallows nothing and changes nothing.
      click (.tag "cb-off")
      assertUnchecked (.tag "cb-off")
      checkEq "disabled checkbox never called back" (← offCalls.get) 0
      -- Clicking the *label text* of a button hits the button through its
      -- merged node's center.
      click (.text "+1")
      assertExists (.text "count: 1")
      click (.text "+1")
      assertExists (.text "count: 2")
      assertMissing (.text "count: 1")

/-! ## Keyboard: focus traversal and activation -/

private def keyboardFlow : IO Unit := do
  let checked ← mutableStateOf false
  let count ← mutableStateOf (0 : Nat)
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      Checkbox (← checked.get) checked.set (modifier := Modifier.testTag "cb")
      Button (count.modify (· + 1)) (modifier := Modifier.testTag "go")
        (content := Text "go")
      Text s!"count: {← count.get}"))
    do
      assertNotFocused (.tag "cb")
      pressKey .tab
      assertFocused (.tag "cb")
      pressKey .space
      assertChecked (.tag "cb")
      pressKey .tab
      assertFocused (.tag "go")
      assertNotFocused (.tag "cb")
      pressKey .return
      assertExists (.text "count: 1")
      pressKey .escape
      assertNotFocused (.tag "go")

/-! ## Text input through the IME commit path -/

private def textFieldFlow : IO Unit := do
  let value ← mutableStateOf ""
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      TextFieldS (← value.get) value.set (modifier := Modifier.testTag "name")
      Text s!"len: {(← value.get).length}"))
    do
      assertTextEquals (.tag "name") ""
      -- typeText click-focuses first (real click-to-focus), then commits
      -- per-codepoint text events through the router.
      typeText (.tag "name") "hi"
      assertFocused (.tag "name")
      check "IME session started by the real focus path"
        (← (← uiTest).ctx.window.textInputActive)
      assertTextEquals (.tag "name") "hi"
      assertExists (.text "len: 2")
      -- Already focused: no re-click, the caret stays at the end.
      typeText (.tag "name") "!"
      assertTextEquals (.tag "name") "hi!"
      pressKey .backspace
      assertTextEquals (.tag "name") "hi"
      checkEq "state saw the edits" (← value.get) "hi"

/-! ## Toggle/selection/range state across the widget set -/

private def widgetStates : IO Unit := do
  let on ← mutableStateOf false
  let choice ← mutableStateOf (0 : Nat)
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      Switch (← on.get) on.set (modifier := Modifier.testTag "sw")
      RadioButton ((← choice.get) == 0) (choice.set 0)
        (modifier := Modifier.testTag "r0")
      RadioButton ((← choice.get) == 1) (choice.set 1)
        (modifier := Modifier.testTag "r1")
      LinearProgressIndicator (some 0.3) (modifier := Modifier.testTag "prog")))
    do
      assertUnchecked (.tag "sw")
      click (.tag "sw")
      assertChecked (.tag "sw")
      assertSelected (.tag "r0")
      assertSelected (.tag "r1") (expected := false)
      click (.tag "r1")
      assertSelected (.tag "r1")
      assertSelected (.tag "r0") (expected := false)
      assertRangeValue (.tag "prog") 0.3
      assertExists ((Matcher.role .progressBar).and (.tag "prog"))

/-! ## Drag and keys on a slider -/

private def sliderDragAndKeys : IO Unit := do
  let value ← mutableStateOf (0.25 : Float32)
  runComposeTest
    (content := Tests.restartable 1 do
      Slider (← value.get) value.set (modifier := Modifier.testTag "sl"))
    do
      assertRangeValue (.tag "sl") 0.25
      -- Window is 320 wide; the slider fills it: track 12..308 (296 px).
      -- A click at the center seeks to 0.5 …
      click (.tag "sl")
      assertRangeValue (.tag "sl") 0.5 (tol := 0.02)
      -- … and a 74 px drag moves a quarter of the track.
      drag (.tag "sl") ⟨74, 0⟩
      assertRangeValue (.tag "sl") 0.75 (tol := 0.02)
      -- The click focused it; End jumps to the range end through key routing.
      assertFocused (.tag "sl")
      pressKey .«end»
      assertRangeValue (.tag "sl") 1.0
      pressKey .left
      assertRangeValue (.tag "sl") 0.99 (tol := 0.001)

/-! ## Wheel scroll through the hit-tested onScroll path -/

private def scrollFlow : IO Unit := runComposeTest
  (content := do
    let st ← rememberScrollState
    Box (Modifier.testTag "scroller" |>.width 60 |>.height 100
          |>.verticalScroll st)
      (content := fun _ => Column {} (content := fun _ => do
        Box (Modifier.size 60 80 |>.testTag "top")
        Spacer (Modifier.size 60 400))))
  do
    assertThat (.tag "top") "starts at the viewport top" (fun n => n.bounds.top == 0)
    -- Two wheel notches toward the content end: 2 × 50 px.
    scrollBy (.tag "scroller") ⟨0, -2⟩
    assertThat (.tag "top") "scrolled 100 px up" (fun n => n.bounds.top == -100)
    -- The viewport clamps at the content end (480 − 100 = 380).
    scrollBy (.tag "scroller") ⟨0, -100⟩
    assertThat (.tag "top") "clamped at maxValue" (fun n => n.bounds.top == -380)
    scrollBy (.tag "scroller") ⟨0, 100⟩
    assertThat (.tag "top") "scrolled back to 0" (fun n => n.bounds.top == 0)

/-! ## The controlled clock drives animation deterministically -/

private def animationClock : IO Unit := do
  let big ← mutableStateOf false
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      let w ← animateDpAsState (if (← big.get) then 200 else 40) (.tween 200 0 .linear)
      Box (Modifier.testTag "box" |>.size (← w.get) 20)
      Button (big.set true) (content := Text "grow")))
    do
      assertThat (.tag "box") "starts at 40" (fun n => rw n.bounds == 40)
      click (.text "grow")
      -- Time is frozen: the animation is launched but hasn't produced a
      -- frame, so the box must not have moved.
      assertThat (.tag "box") "unmoved while the clock is frozen"
        (fun n => rw n.bounds == 40)
      awaitIdle
      assertThat (.tag "box") "still unmoved after idling"
        (fun n => rw n.bounds == 40)
      -- Half the tween: strictly between the endpoints.
      advanceTimeBy 104
      assertThat (.tag "box") "mid-tween after advanceTimeBy 104"
        (fun n => 60 < rw n.bounds && rw n.bounds < 180)
      -- Past the end: exactly the target, and stable.
      advanceTimeBy 200
      assertThat (.tag "box") "settled at 200" (fun n => rw n.bounds == 200)
      settle
      assertThat (.tag "box") "stable after settle" (fun n => rw n.bounds == 200)

/-! ## Overlays: alert dialog in the semantics tree -/

private def dialogFlow : IO Unit := do
  let open' ← mutableStateOf false
  let confirmed ← IO.mkRef false
  runComposeTest
    (content := Tests.restartable 1 do
      Button (open'.set true) (content := Text "open")
      if ← open'.get then
        AlertDialog (onDismissRequest := open'.set false) (title := "Sure?")
          (text := "Really do it?")
          (confirmButton := TextButton
            (do confirmed.set true; open'.set false) (content := Text "Yes")))
    do
      assertMissing (.role .dialog)
      click (.text "open")
      assertExists (.role .dialog)
      assertExists (.text "Sure?")
      -- The dialog's button is an overlay layer — same finders, same clicks.
      click (.text "Yes")
      assertMissing (.role .dialog)
      check "dialog confirm callback ran" (← confirmed.get)

/-! ## Modal focus is scoped to the dialog, restored on close -/

private def dialogFocusScope : IO Unit := do
  let open' ← mutableStateOf false
  runComposeTest
    (content := Tests.restartable 1 do
      Column {} (content := fun _ => do
        Button (open'.set true) (modifier := Modifier.testTag "bg") (content := Text "open")
        if ← open'.get then
          AlertDialog (onDismissRequest := open'.set false) (title := "T") (text := "B")
            (confirmButton := TextButton (open'.set false)
              (modifier := Modifier.testTag "ok") (content := Text "OK"))))
    do
      -- The opener is clicked (and focused) — then it opens the dialog.
      click (.tag "bg")
      settle
      assertExists (.role .dialog)
      -- Tab lands *inside* the dialog and stays there (scoped past the scrim),
      -- never reaching the background button.
      pressKey .tab
      assertFocused (.tag "ok")
      pressKey .tab
      assertFocused (.tag "ok")
      -- Closing restores the focus that was held when the dialog opened.
      click (.tag "ok")
      settle
      assertMissing (.role .dialog)
      assertFocused (.tag "bg")

/-! ## animateScrollTo is a MutatorMutex: the last caller wins -/

private def scrollAnimateInterrupt : IO Unit := do
  let st ← ScrollState.create
  runComposeTest
    (content :=
      Box (Modifier.testTag "sc" |>.width 60 |>.height 100 |>.verticalScroll st)
        (content := fun _ => Column {} (content := fun _ =>
          Spacer (Modifier.size 60 500))))
    do
      awaitIdle  -- measure runs: content 500, viewport 100 ⇒ maxValue 400
      let t ← uiTest
      -- A long scroll toward the end; let it get partway.
      let _ ← t.sched.launch (st.animateScrollTo 400)
      advanceTimeBy 100
      let mid ← st.valueState.cell.get
      check s!"scroll anim: progressed partway toward 400 ({mid})" (mid > 5 && mid < 395)
      -- A shorter interrupting animation to 200: it takes the mutation lock.
      let _ ← t.sched.launch (st.animateScrollTo 200 (.tween 40 0 .linear))
      advanceTimeBy 60
      check s!"scroll anim: interrupt reached its target ({← st.valueState.cell.get})"
        ((← st.valueState.cell.get) == 200)
      -- The cancelled first animation does NOT resume and drag on toward 400.
      advanceTimeBy 300
      check s!"scroll anim: cancelled first stays put ({← st.valueState.cell.get})"
        ((← st.valueState.cell.get) == 200)

/-! ## Overlays: dropdown menu items are real, clickable nodes -/

private def menuFlow : IO Unit := do
  let expanded ← mutableStateOf false
  let picked ← mutableStateOf "-"
  runComposeTest
    (content := Column {} (content := fun _ => Tests.restartable 1 do
      Button (expanded.set true) (content := Text "menu")
      DropdownMenu (← expanded.get) (onDismissRequest := expanded.set false)
        (content := do
          DropdownMenuItem "One" (do picked.set "One"; expanded.set false)
          DropdownMenuItem "Two" (do picked.set "Two"; expanded.set false))
      Text s!"picked: {← picked.get}"))
    do
      assertMissing (.role .menuItem)
      click (.text "menu")
      settle  -- let the enter transition finish so items reach full size
      assertCountEquals (.role .menuItem) 2
      click ((Matcher.text "Two").and (.role .menuItem))
      assertExists (.text "picked: Two")
      -- The exit transition keeps the menu mounted until it finishes…
      assertExists (.role .menuItem)
      settle
      -- …then it leaves the composition.
      assertMissing (.role .menuItem)

/-- The UiTest group. -/
def run : IO Unit := do
  scenario "findersAndFailures" findersAndFailures
  scenario "clickThroughRouter" clickThroughRouter
  scenario "keyboardFlow" keyboardFlow
  scenario "textFieldFlow" textFieldFlow
  scenario "widgetStates" widgetStates
  scenario "sliderDragAndKeys" sliderDragAndKeys
  scenario "scrollFlow" scrollFlow
  scenario "animationClock" animationClock
  scenario "dialogFlow" dialogFlow
  scenario "dialogFocusScope" dialogFocusScope
  scenario "scrollAnimateInterrupt" scrollAnimateInterrupt
  scenario "menuFlow" menuFlow

end Tests.UiTest
