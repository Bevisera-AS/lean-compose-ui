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
    Harness.passes.modify (· + 1)
    IO.println s!"ok {label}"

/-- Width of a rect (bounds assertions). -/
private def rw (r : Compose.Rect) : Float32 := r.right - r.left

/-! ## Finders, merging, failure dumps -/

private def findersAndFailures : IO Unit := runComposeTest
  (Column do
    Text "alpha"
    Text "dup"
    Text "dup"
    Button (pure ()) (Text "go") (modifier := Modifier.testTag "go-btn")
    Button (pure ()) (Text "nope") (enabled := false)
      (modifier := Modifier.testTag "no-btn"))
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
  let checked ← MutableState.create false
  let offCalls ← IO.mkRef (0 : Nat)
  let count ← MutableState.create (0 : Nat)
  runComposeTest
    (Column (Tests.restartable 1 do
      Checkbox (← checked.get) checked.set (modifier := Modifier.testTag "cb")
      Checkbox false (fun _ => offCalls.modify (· + 1)) (enabled := false)
        (modifier := Modifier.testTag "cb-off")
      Button (count.modify (· + 1)) (Text "+1")
      Text s!"count: {← count.get}")) do
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
  let checked ← MutableState.create false
  let count ← MutableState.create (0 : Nat)
  runComposeTest
    (Column (Tests.restartable 1 do
      Checkbox (← checked.get) checked.set (modifier := Modifier.testTag "cb")
      Button (count.modify (· + 1)) (Text "go") (modifier := Modifier.testTag "go")
      Text s!"count: {← count.get}")) do
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
  let value ← MutableState.create ""
  runComposeTest
    (Column (Tests.restartable 1 do
      TextField (← value.get) value.set (modifier := Modifier.testTag "name")
      Text s!"len: {(← value.get).length}")) do
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
  let on ← MutableState.create false
  let choice ← MutableState.create (0 : Nat)
  runComposeTest
    (Column (Tests.restartable 1 do
      Switch (← on.get) on.set (modifier := Modifier.testTag "sw")
      RadioButton ((← choice.get) == 0) (choice.set 0)
        (modifier := Modifier.testTag "r0")
      RadioButton ((← choice.get) == 1) (choice.set 1)
        (modifier := Modifier.testTag "r1")
      LinearProgressIndicator (some 0.3) (modifier := Modifier.testTag "prog"))) do
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
  let value ← MutableState.create (0.25 : Float32)
  runComposeTest
    (Tests.restartable 1 do
      Slider (← value.get) value.set (modifier := Modifier.testTag "sl")) do
      assertRangeValue (.tag "sl") 0.25
      -- Window is 480 wide; the slider fills it: track 12..468 (456 px).
      -- A click at the center seeks to 0.5 …
      click (.tag "sl")
      assertRangeValue (.tag "sl") 0.5 (tol := 0.02)
      -- … and a 114 px drag moves a quarter of the track.
      drag (.tag "sl") ⟨114, 0⟩
      assertRangeValue (.tag "sl") 0.75 (tol := 0.02)
      -- The click focused it; End jumps to the range end through key routing.
      assertFocused (.tag "sl")
      pressKey .«end»
      assertRangeValue (.tag "sl") 1.0
      pressKey .left
      assertRangeValue (.tag "sl") 0.99 (tol := 0.001)

/-! ## Wheel scroll through the hit-tested onScroll path -/

private def scrollFlow : IO Unit := runComposeTest
  (do
    let st ← rememberScrollState
    Box (modifier := Modifier.testTag "scroller" |>.width 60 |>.height 100
          |>.verticalScroll st) do
      Column do
        Box (modifier := Modifier.size 60 80 |>.testTag "top")
        Spacer (Modifier.size 60 400))
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
  let big ← MutableState.create false
  runComposeTest
    (Column (Tests.restartable 1 do
      let w ← animateDpAsState (if (← big.get) then 200 else 40) (.tween 200 0 .linear)
      Box (modifier := Modifier.testTag "box" |>.size (← w.get) 20)
      Button (big.set true) (Text "grow"))) do
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

/-! ## M14b verbs: replaceText and requestFocus -/

private def replaceAndFocusVerbs : IO Unit := do
  let value ← MutableState.create "seed"
  runComposeTest
    (Column (Tests.restartable 1 do
      TextField (← value.get) value.set (modifier := Modifier.testTag "tf")
      Box (modifier := Modifier.testTag "target" |>.size 60 20 |>.focusable))) do
      assertTextEquals (.tag "tf") "seed"
      replaceText (.tag "tf") "fresh"          -- select-all + retype, not append
      assertTextEquals (.tag "tf") "fresh"
      replaceText (.tag "tf") ""               -- empty replacement clears
      assertTextEquals (.tag "tf") ""
      requestFocus (.tag "target")             -- focus without a click
      assertFocused (.tag "target")
      assertNotFocused (.tag "tf")

/-! ## Programmatic focus: FocusRequester from handlers and effects -/

private def focusRequesterFlow : IO Unit := do
  runComposeTest
    (do
      let frA ← rememberFocusRequester
      let frB ← rememberFocusRequester
      -- An effect can grab initial focus before any user input.
      LaunchedEffect 0 frB.requestFocus
      Column do
        Box (modifier := Modifier.testTag "a" |>.size 60 20 |>.focusable |>.focusRequester frA)
        Box (modifier := Modifier.testTag "b" |>.size 60 20 |>.focusable |>.focusRequester frB)
        Button frA.requestFocus (Text "focus a") (modifier := Modifier.testTag "grab")) do
      assertFocused (.tag "b")                -- the launch-time request landed
      -- A handler moves focus after its own click-to-focus ran.
      click (.tag "grab")
      assertFocused (.tag "a")
      assertNotFocused (.tag "b")
      -- Tab traversal keeps working from the programmatic position.
      pressKey .tab
      assertFocused (.tag "b")

/-! ## Overlays: alert dialog in the semantics tree -/

private def dialogFlow : IO Unit := do
  let open' ← MutableState.create false
  let confirmed ← IO.mkRef false
  runComposeTest
    (Tests.restartable 1 do
      Button (open'.set true) (Text "open")
      if ← open'.get then
        AlertDialog (onDismissRequest := open'.set false) (title := "Sure?")
          (text := "Really do it?")
          (confirmButton := TextButton
            (do confirmed.set true; open'.set false) (Text "Yes"))) do
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
  let open' ← MutableState.create false
  runComposeTest
    (Tests.restartable 1 do
      Column do
        Button (open'.set true) (Text "open") (modifier := Modifier.testTag "bg")
        if ← open'.get then
          AlertDialog (onDismissRequest := open'.set false) (title := "T") (text := "B")
            (confirmButton := TextButton (open'.set false) (Text "OK")
              (modifier := Modifier.testTag "ok"))) do
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
    (Box (modifier := Modifier.testTag "sc" |>.width 60 |>.height 100 |>.verticalScroll st) do
      Column (Spacer (Modifier.size 60 500))) do
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
  let expanded ← MutableState.create false
  let picked ← MutableState.create "-"
  runComposeTest
    (Column (Tests.restartable 1 do
      Button (expanded.set true) (Text "menu")
      DropdownMenu (← expanded.get) (onDismissRequest := expanded.set false) do
        DropdownMenuItem "One" (do picked.set "One"; expanded.set false)
        DropdownMenuItem "Two" (do picked.set "Two"; expanded.set false)
      Text s!"picked: {← picked.get}")) do
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
  scenario "replaceAndFocusVerbs" replaceAndFocusVerbs
  scenario "focusRequesterFlow" focusRequesterFlow
  scenario "animationClock" animationClock
  scenario "dialogFlow" dialogFlow
  scenario "dialogFocusScope" dialogFocusScope
  scenario "scrollAnimateInterrupt" scrollAnimateInterrupt
  scenario "menuFlow" menuFlow

end Tests.UiTest
