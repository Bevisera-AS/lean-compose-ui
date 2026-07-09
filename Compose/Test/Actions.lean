import Compose.Test.Finders

namespace Compose.Test

/-!
# Actions (`Compose/Test/Actions.lean`)

Interactions with found nodes. Every action synthesizes SDL events and pushes
them through the production input path (`dispatchEvent` → `inputSink` →
`InputManager.sdlEvent` → hit test → gesture coroutines / focus / key
routing) — nothing invokes a widget callback directly, so a passing test
proves the whole event pipeline, and a widget whose hit region is broken
fails its click test exactly as it would fail a user. Positions come from
the node's *real laid-out bounds*. Every action ends with `awaitIdle`.

Mirrors `performClick` / `performTextInput` / `performKeyPress` /
`performTouchInput { swipe }` / `performScrollBy` — as `TestM` verbs taking
the `Matcher` first: `click (.text "OK")`.
-/

/-- Click at `pos` (render coordinates): press + release through the router.
The escape hatch when clicking *empty space* matters (dismiss regions). -/
def clickAt (pos : Offset) (button : Sdl.MouseButton := .left) : TestM Unit := do
  mouseDown pos button
  mouseUp pos button
  awaitIdle

/-- Click the unique matching node at its center. Mirrors `performClick`. -/
def click (m : Matcher) (button : Sdl.MouseButton := .left) : TestM Unit := do
  clickAt (← boundsOf m).center button

/-- Double-click the node's center: two press/release pairs with SDL's
consecutive-click counter at 1 then 2, exactly what a real double-click
delivers. -/
def doubleClick (m : Matcher) : TestM Unit := do
  let c := (← boundsOf m).center
  mouseDown c (clicks := 1); mouseUp c (clicks := 1)
  mouseDown c (clicks := 2); mouseUp c (clicks := 2)
  awaitIdle

/-- Move the pointer to the node's center (hover enter/move on the way).
Mirrors `performMouseInput { moveTo }`. -/
def moveTo (m : Matcher) : TestM Unit := do
  mouseMove (← boundsOf m).center
  awaitIdle

/-- Press at the node's center, drag by `delta` in `steps` intermediate
moves, and release — a full drag gesture through the router's capture path.
Mirrors `performTouchInput { swipeBy }`. -/
def drag (m : Matcher) (delta : Offset) (steps : Nat := 4) : TestM Unit := do
  let start := (← boundsOf m).center
  mouseDown start
  let steps := max steps 1
  for i in [1:steps + 1] do
    mouseMove (start + delta * (i.toFloat32 / steps.toFloat32))
  mouseUp (start + delta)
  awaitIdle

/-- Wheel-scroll over the node's center; `delta` is in wheel ticks
(positive `y` = away from the user = content scrolls up). Mirrors
`performMouseInput { scroll }`. -/
def scrollBy (m : Matcher) (delta : Offset) : TestM Unit := do
  mouseWheel (← boundsOf m).center delta
  awaitIdle

/-- Press and release one key (modifiers held for both), routed
focused-node-first like real keys. Mirrors `performKeyPress`. -/
def pressKey (key : Sdl.Keycode) (mods : Sdl.Keymod := .none) : TestM Unit := do
  keyDown key mods
  keyUp key mods
  awaitIdle

/-- Type `text` into the matching node through the committed-text (IME)
path, one codepoint per event like a human typist. If the node is not
already focused, it is first clicked at its center (real click-to-focus).
Mirrors `performTextInput` (which also requests focus first). -/
def typeText (m : Matcher) (text : String) : TestM Unit := do
  let n ← find m
  let alreadyFocused ← do
    match ← focusedNode with
    | some f => do pure ((← f.nodeId) == (← n.layout.nodeId))
    | none => pure false
  unless alreadyFocused do
    clickAt n.bounds.center
  for c in text.toList do
    textInput c.toString
  awaitIdle

/-- Replace the matching text field's content with `text`: focus it (a real
click when needed), select all (Ctrl-A through the editing keymap), then
type — the selection makes the first codepoint replace everything; an empty
`text` clears via Backspace. Mirrors `performTextReplacement`. -/
def replaceText (m : Matcher) (text : String) : TestM Unit := do
  typeText m ""                        -- focus through the real input path
  pressKey .a (mods := Sdl.Keymod.lCtrl)
  if text.isEmpty then
    pressKey .backspace
  else
    typeText m text

/-- Move keyboard focus straight to the unique matching node — the
programmatic seam for tests that need focus without a click (the node must
still be focusable for keys to route as in production). Mirrors
`SemanticsNodeInteraction.requestFocus`. -/
def requestFocus (m : Matcher) : TestM Unit := do
  let n ← find m
  (← uiTest).input.focus.requestFocus (some n.layout)
  awaitIdle

end Compose.Test
