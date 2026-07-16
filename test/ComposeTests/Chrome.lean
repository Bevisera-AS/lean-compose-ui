import Compose
import ComposeTests.Harness

/-!
# Chrome test group (`test/ComposeTests/Chrome.lean`)

The app-chrome widget wave: `Icon` (path tint), `FilterChip` (toggle +
semantics), `ListItem` (slots), `Scaffold`/`TopAppBar` (stacking),
`LazyRow` (horizontal windowing), and `ModalBottomSheet` (open, back-
dismiss, drag-dismiss).
-/

namespace Tests.Chrome
open Compose Compose.Test Tests.Harness

private def pressBack : TestM Unit :=
  sendEvent (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, .acBack, .none, 0, true, false⟩)

/-- Icon draws its path in the tint color: the `close` X crosses dead
center; probe that pixel. -/
private def iconTint : IO Unit := do
  runComposeTest
    (Box do
      Icon Material.Icons.close (tint := some (.hex 0xFFFF0000))
        (contentDescription := some "close icon"))
    (do
      awaitIdle
      let px ← pixel 12 12
      check "icon: center pixel tinted red"
        (px.r > 200 && px.g < 60 && px.b < 60)
      assertExists (.pred "desc \"close icon\"" (·.props.contentDescription == some "close icon")))

/-- FilterChip: click toggles through onClick; the checkbox role and
toggled flag ride the semantics tree. -/
private def chipToggle : IO Unit := do
  let sel ← MutableState.create false
  runComposeTest
    (do
      FilterChip (← sel.get) (sel.modify (!·)) "Dual"
        (modifier := Modifier.testTag "chip"))
    (do
      assertExists (.tag "chip")
      click (.tag "chip")
      awaitIdle
      checkEq "chip: click toggled the state" (← sel.get) true
      click (.tag "chip")
      awaitIdle
      checkEq "chip: click toggles back" (← sel.get) false)

/-- ListItem: headline, supporting text, and both slots compose. -/
private def listItemSlots : IO Unit := do
  runComposeTest
    (ListItem "Session 12" (supporting := some "n = 3 · 85%")
      (leading := some (Icon Material.Icons.check))
      (trailing := some (Text "›" (modifier := Modifier.testTag "trail"))))
    (do
      assertExists (.text "Session 12")
      assertExists (.text "n = 3 · 85%")
      assertExists (.tag "trail"))

/-- Scaffold stacks the top bar above the weighted content. -/
private def scaffoldStack : IO Unit := do
  runComposeTest
    (Scaffold
      (topBar := some (TopAppBar "NBack"
        (navigationIcon := some (IconButton (pure ()) Material.Icons.arrowBack
          (modifier := Modifier.testTag "nav")))
        (actions := some (IconButton (pure ()) Material.Icons.settings
          (modifier := Modifier.testTag "act")))))
      (content := Text "body" (modifier := Modifier.testTag "body")))
    (do
      assertExists (.text "NBack")
      assertExists (.tag "nav")
      assertExists (.tag "act")
      let bar ← boundsOf (.text "NBack")
      let body ← boundsOf (.tag "body")
      check "scaffold: content below the bar" (body.top ≥ bar.bottom))

/-- LazyRow windows horizontally: far items are not composed until the row
scrolls to them. -/
private def lazyRowWindow : IO Unit := do
  let state ← ScrollState.create
  runComposeTest
    (do
      LazyRow state 40 100 (modifier := Modifier.size 200 50)
        (itemContent := fun i =>
          Text s!"i{i}" (modifier := Modifier.testTag s!"i{i}")))
    (do
      assertExists (.tag "i0")
      assertExists (.tag "i4")
      assertMissing (.tag "i8")
      liftM (state.scrollTo 400)   -- 10 items right
      awaitIdle
      assertMissing (.tag "i0")
      assertExists (.tag "i10")
      assertExists (.tag "i14"))

/-- ModalBottomSheet: opens with content, back dismisses, and a past-
threshold downward drag dismisses. -/
private def bottomSheet : IO Unit := do
  let open_ ← MutableState.create true
  runComposeTest
    (do
      if ← open_.get then
        ModalBottomSheet (open_.set false) (content := do
          Text "sheet content" (modifier := Modifier.testTag "sheet")))
    (do
      settle
      assertExists (.tag "sheet")
      pressBack
      awaitIdle
      checkEq "sheet: back dismissed" (← open_.get) false
      assertMissing (.tag "sheet")
      liftM (open_.set true)
      settle
      assertExists (.tag "sheet")
      -- drag the sheet body down past the 96dp threshold
      drag (.tag "sheet") ⟨0, 150⟩
      awaitIdle
      checkEq "sheet: drag past threshold dismissed" (← open_.get) false)

/-- `isSystemInDarkTheme` is live: flipping the shell state recomposes
readers (the dummy video driver reports no theme, so the test drives the
state the `systemThemeChanged` handler writes; the handler itself is a
re-read of `Sdl.getSystemTheme`). -/
private def darkThemeLive : IO Unit := do
  runComposeTest
    (do
      Text (if ← isSystemInDarkTheme then "dark" else "light")
        (modifier := Modifier.testTag "theme"))
    (do
      assertTextEquals (.tag "theme") "light"
      liftM (systemDarkState.set true)
      awaitIdle
      assertTextEquals (.tag "theme") "dark"
      -- the event path routes without error under the dummy driver
      sendEvent (.systemThemeChanged ⟨0⟩)
      awaitIdle
      liftM (systemDarkState.set false))

/-- Locale resolution is live: pushing a new preferred-locale list
recomposes readers through `resolveLocale` (the same shell-state pattern
the `localeChanged` handler drives). -/
private def localeLive : IO Unit := do
  runComposeTest
    (do
      let tag ← resolveLocale #[⟨"en", none⟩, ⟨"vi", none⟩]
      Text (if tag == some ⟨"vi", none⟩ then "xin chào" else "hello")
        (modifier := Modifier.testTag "greet"))
    (do
      liftM (preferredLocalesState.set #[⟨"fr", none⟩])
      awaitIdle
      assertTextEquals (.tag "greet") "hello"     -- no match → default
      liftM (preferredLocalesState.set #[⟨"vi", some "VN"⟩])
      awaitIdle
      assertTextEquals (.tag "greet") "xin chào"  -- language match, live
      liftM (preferredLocalesState.set #[]))

def run : IO Unit := do
  iconTint
  chipToggle
  listItemSlots
  scaffoldStack
  lazyRowWindow
  bottomSheet
  darkThemeLive
  localeLive

end Tests.Chrome
