import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Material test group (`test/ComposeTests/Material.lean`)

M9's theme + widget suites, headless (dummy video driver, software
renderer). Composition-level checks (theme locals, Surface's content-color
contract) run on plain compositions; everything visual/interactive runs in a
bootstrapped window whose *content* is composed under a **fake-clock
scheduler** (`LocalScheduler` provider, the Input/Animation-group pattern),
so gesture coroutines and animations are driven deterministically by manual
`runDue`/`tickFrame` while `step` renders pixels for probing. Synthetic
input goes through `dispatchEvent` (constructed `Sdl.Event`s), the same path
the real loop uses.
-/

namespace Tests.Material
open Compose Compose.Test Tests.Harness

/-- Test config: software renderer for stable `readPixels`, no vsync. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

/-- The light baseline scheme all probes compare against. -/
private def L : ColorScheme := .light

/-- Whether an SDL pixel is within `tol` byte-steps of a theme color. -/
private def near (c : Sdl.Color) (e : Compose.Color) (tol : Nat := 4) : Bool :=
  let (r, g, b, _) := e.toBytes
  colorNear c r g b tol

/-- `fg` composited over an opaque white background (what a translucent
container renders to on the test clear color). -/
private def overWhite (fg : Compose.Color) : Compose.Color :=
  fg.compositeOver .white

/-- `|x − y| ≤ tol` for runtime float checks. -/
private def approx (x y : Float32) (tol : Float32 := 0.02) : Bool := (x - y).abs ≤ tol

/-! ## Theme locals (plain composition) -/

/-- `MaterialTheme` provides scheme/typography/shapes and re-seeds
`LocalTextStyle`/`LocalContentColor`; a nested theme overrides what it
names — for its subtree only — and **inherits** the rest from the ambient
theme. -/
private def themeLocals : IO Unit := do
  let t ← TestTree.create
  let lightCap ← IO.mkRef (none : Option (ColorScheme × TextStyle × Compose.Color × Shapes))
  let darkCap ← IO.mkRef (none : Option (ColorScheme × TextStyle × Compose.Color))
  let afterCap ← IO.mkRef (none : Option ColorScheme)
  let _ ← Composition.create t.applier <| MaterialTheme
    (typography := some { bodyMedium := { fontSize := 16 } }) do
    lightCap.set (some (← MaterialTheme.colorScheme, ← LocalTextStyle.current,
      ← LocalContentColor.current, ← MaterialTheme.shapes))
    MaterialTheme (colors := some .dark) do
      darkCap.set (some (← MaterialTheme.colorScheme, ← LocalTextStyle.current,
        ← LocalContentColor.current))
    afterCap.set (some (← MaterialTheme.colorScheme))
  let some (cs, ts, cc, sh) ← lightCap.get | throw (IO.userError "light capture missing")
  check "theme: colorScheme is the light baseline" (cs == .light)
  check "theme: LocalTextStyle takes the custom bodyMedium size" (ts.fontSize == (16 : Sp))
  check "theme: LocalTextStyle colored onSurface" (ts.color == L.onSurface)
  check "theme: LocalContentColor seeded with onSurface" (cc == L.onSurface)
  check "theme: shapes provided" (sh.small == Shape.rounded 8)
  let some (dcs, dts, dcc) ← darkCap.get | throw (IO.userError "dark capture missing")
  check "theme: nested dark scheme overrides" (dcs == .dark)
  check "theme: nested dark text style recolored" (dts.color == ColorScheme.dark.onSurface)
  check "theme: nested dark content color" (dcc == ColorScheme.dark.onSurface)
  check "theme: nested dark inherits the outer custom typography"
    (dts.fontSize == (16 : Sp))
  let some acs ← afterCap.get | throw (IO.userError "after capture missing")
  check "theme: dark subtree does not leak to its sibling" (acs == .light)

/-- The `Theme` bundle installs wholesale, `MaterialTheme.current` reads it
back, a nested per-aspect override inherits everything it does not name, and
`LocalScrimColor` follows the scheme at the theme's scrim opacity. -/
private def themeBundle : IO Unit := do
  let t ← TestTree.create
  let custom : Theme :=
    { colors := .dark
      typography := { bodyMedium := { fontSize := 17 } }
      tokens := { scrimAlpha := 0.5, elevations := { dialog := 9 } } }
  let outerCap ← IO.mkRef (none : Option (Theme × Compose.Color))
  let innerCap ← IO.mkRef (none : Option Theme)
  let _ ← Composition.create t.applier <| MaterialTheme (theme := some custom) do
    outerCap.set (some (← MaterialTheme.current, ← LocalScrimColor.current))
    MaterialTheme (colors := some .light) do
      innerCap.set (some (← MaterialTheme.current))
  let some (outer, oscrim) ← outerCap.get | throw (IO.userError "outer capture missing")
  check "theme: bundle round-trips through MaterialTheme.current" (outer == custom)
  check "theme: scrim local follows the scheme at the theme's opacity"
    (oscrim == custom.colors.scrim.withAlpha 0.5)
  let some inner ← innerCap.get | throw (IO.userError "inner capture missing")
  check "theme: nested colors-only override inherits typography and tokens"
    (inner == { custom with colors := .light })

/-- `Surface` provides the `on*` pair of its container color (and recolors
the ambient text style); a non-scheme color inherits the ambient content
color. -/
private def surfaceContentColor : IO Unit := do
  let root ← LayoutNode.create
  let primaryCap ← IO.mkRef (none : Option (Compose.Color × Compose.Color))
  let unknownCap ← IO.mkRef (none : Option Compose.Color)
  let _ ← Composition.create (LayoutNode.applier root) <| MaterialTheme do
    Surface (color := some L.primary) do
      primaryCap.set (some (← LocalContentColor.current, (← LocalTextStyle.current).color))
    Surface (color := some .magenta) do
      unknownCap.set (some (← LocalContentColor.current))
  let some (cc, tc) ← primaryCap.get | throw (IO.userError "surface capture missing")
  check "surface: primary container gives onPrimary content" (cc == L.onPrimary)
  check "surface: text style recolored to the content color" (tc == L.onPrimary)
  let some ucc ← unknownCap.get | throw (IO.userError "surface capture missing")
  check "surface: non-scheme color inherits the ambient content color"
    (ucc == L.onSurface)

/-! ## Windowed rig: fake-clock scheduler inside a bootstrapped window -/

private structure MRig where
  ctx : WindowContext
  s : Scheduler
  clock : IO.Ref UInt64

/-- Bootstrap `content` under a fake-clock `LocalScheduler` (gestures and
animations run on it; the window's own scheduler idles), start the queued
coroutines, and render the first frame. -/
private def mboot (content : Composable Unit) (w : Dp := 240) (h : Dp := 160) :
    IO MRig := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  let ctx ← bootstrap "compose-material-test" w h
    (CompositionLocalProvider LocalScheduler (some s) content) cfg
  let _ ← step ctx cfg
  s.runDue 0
  return { ctx, s, clock }

/-- Render if anything is dirty (recompose → remeasure → draw). -/
private def MRig.render (r : MRig) : IO Unit := do
  if ← r.ctx.needsFrame.get then
    let _ ← step r.ctx cfg

/-- Advance the fake clock by `dtMs`, run due coroutines, tick the frame
clock, and render. Drives one animation frame deterministically. -/
private def MRig.tick (r : MRig) (dtMs : UInt64) : IO Unit := do
  let t := (← r.clock.get) + dtMs * 1_000_000
  r.clock.set t
  r.s.runDue t
  r.s.tickFrame t
  r.render

/-- Settle: apply pending recompositions (launching any queued animation
coroutines), then tick 8 ms frames until no frame-clock work remains (cap
2.4 s of fake time), and render the final state. -/
private def MRig.settle (r : MRig) : IO Unit := do
  r.render
  r.s.runDue (← r.clock.get)
  let mut i := 0
  while (← r.s.hasFrameWork) && i < 300 do
    let t := (← r.clock.get) + 8 * 1_000_000
    r.clock.set t
    r.s.runDue t
    r.s.tickFrame t
    i := i + 1
  r.render

private def MRig.pixel (r : MRig) (x y : Int32) : IO Sdl.Color := do
  (← (← r.ctx.sdlRenderer).readPixels).readPixel x y

private def MRig.send (r : MRig) (e : Sdl.Event) : IO Unit :=
  dispatchEvent r.ctx cfg e

private def MRig.press (r : MRig) (x y : Float32) : IO Unit :=
  r.send (.mouseButtonDown ⟨0, ⟨0⟩, ⟨0⟩, .left, true, 1, x, y⟩)

private def MRig.release (r : MRig) (x y : Float32) : IO Unit :=
  r.send (.mouseButtonUp ⟨0, ⟨0⟩, ⟨0⟩, .left, false, 1, x, y⟩)

private def MRig.click (r : MRig) (x y : Float32) : IO Unit := do
  r.press x y
  r.release x y

private def MRig.move (r : MRig) (x y : Float32) : IO Unit :=
  r.send (.mouseMotion ⟨0, ⟨0⟩, ⟨0⟩, .none, x, y, 0, 0⟩)

private def MRig.key (r : MRig) (k : Sdl.Keycode) : IO Unit :=
  r.send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .unknown, k, .none, 0, true, false⟩)

/-- Wrap widget content in the theme (the widgets require it only for
colors — defaults — but tests pin the light baseline). -/
private def themed (content : Composable Unit) : Composable Unit :=
  MaterialTheme content

/-! ## Button -/

/-- Filled button: container/label pixels, click activation, focus +
Enter/Space activation. -/
private def buttonBasics : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let r ← mboot <| themed <| Button (clicks.modify (· + 1)) (Text "OK")
  let sz ← (← r.ctx.root.child 0).size
  check s!"button: sized to label + padding, min height ({sz.width}x{sz.height})"
    (sz.width ≥ 64 && sz.height == 40)
  let cx := sz.width.toFloat32 / 2
  check "button: container pixel is primary" (near (← r.pixel 12 20) L.primary)
  let bg ← r.pixel 230 100
  check s!"button: outside is the clear color ({showColor bg})" (near bg .white)
  -- Label glyphs: onPrimary (white-ish) pixels inside the container.
  let surf ← (← r.ctx.sdlRenderer).readPixels
  let mut glyph := 0
  for y in [10:30] do
    for x in [12:sz.width.toNatClampNeg - 12] do
      let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if c.r > 220 && c.g > 220 && c.b > 220 then glyph := glyph + 1
  check s!"button: onPrimary label glyphs present ({glyph})" (glyph > 0)
  -- Mouse click.
  r.click cx 20
  r.settle
  checkEq "button: click fires onClick" (← clicks.get) 1
  -- Keyboard: Tab focuses, Enter and Space activate.
  r.key .tab
  r.settle
  r.key .return
  r.key .space
  checkEq "button: Enter/Space activate when focused" (← clicks.get) 3

/-- Hovering animates the state layer: the container pixel brightens toward
the 8 % onPrimary overlay. -/
private def buttonHoverLayer : IO Unit := do
  let r ← mboot <| themed <| Button (pure ()) (Text "OK")
  let before ← r.pixel 12 20
  check "hover: starts at plain primary" (near before L.primary)
  r.move 20 20
  r.settle
  let after ← r.pixel 12 20
  let expected := (Compose.Color.white.withAlpha stateLayerHoverAlpha).compositeOver L.primary
  check s!"hover: settled pixel is primary + 8% white ({showColor after})"
    (near after expected)
  check "hover: pixels actually changed" (after.r.toNat > before.r.toNat + 5)
  -- Moving off animates back down.
  r.move 230 140
  r.settle
  check "hover: unhover returns to plain primary" (near (← r.pixel 12 20) L.primary)

/-- A held press shows the bounded ripple: the container brightens (ripple +
press layer) while the rounded corner outside the shape stays background —
the expanding circle is geometrically clipped. Releasing fades it back. -/
private def buttonPressRipple : IO Unit := do
  -- Green backdrop behind the button: an *unclipped* white ripple would
  -- visibly whiten the corner pixel outside the rounded shape.
  let r ← mboot <| themed <| Box (Button (pure ()) (Text "OK"))
    (modifier := Modifier.fillMaxSize |>.background .green)
  let before ← r.pixel 40 20
  r.press 12 20
  r.settle    -- ripple expands to cover, alpha held while pressed
  let held ← r.pixel 40 20
  check s!"ripple: container brightens while pressed ({showColor before} → {showColor held})"
    (held.r.toNat ≥ before.r.toNat + 8)
  -- The press circle (r ≈ cover radius from (12,20)) would cover (0,0) if
  -- it were not clipped to the button's rounded shape (the pixel is outside
  -- the r=8 corner arc and beyond its 1 px AA feather).
  let corner ← r.pixel 0 0
  check s!"ripple: clipped to the shape — corner stays backdrop ({showColor corner})"
    (near corner .green)
  r.release 12 20
  r.settle    -- ripple fades out (hover layer may remain)
  let after ← r.pixel 40 20
  check s!"ripple: fades after release ({showColor held} → {showColor after})"
    (after.r.toNat + 4 ≤ held.r.toNat)

/-- Disabled button: dimmed container, no click, no focus. -/
private def buttonDisabled : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let r ← mboot <| themed <|
    Button (clicks.modify (· + 1)) (enabled := false) (Text "OK")
  let expected := overWhite (L.onSurface.withAlpha disabledContainerAlpha)
  let px ← r.pixel 12 20
  check s!"disabled button: container dimmed to onSurface@12% ({showColor px})"
    (near px expected)
  r.click 30 20
  r.settle
  checkEq "disabled button: click does nothing" (← clicks.get) 0
  r.key .tab
  r.key .return
  r.settle
  checkEq "disabled button: not focusable, keys do nothing" (← clicks.get) 0

/-! ## Checkbox / RadioButton / Switch -/

/-- Checkbox: click and Space toggle with correct callback values; the
checked visuals settle to a primary box with an onPrimary mark. -/
private def checkboxToggles : IO Unit := do
  let checked ← MutableState.create false
  let calls ← IO.mkRef (#[] : Array Bool)
  let r ← mboot <| themed <| Tests.restartable 1 do
    let c ← checked.get
    Checkbox c (fun v => do calls.modify (·.push v); checked.set v)
  check "checkbox: unchecked box interior is empty" (near (← r.pixel 15 15) .white)
  check "checkbox: unchecked border stroke present" (near (← r.pixel 20 12) L.onSurfaceVariant 30)
  r.click 20 20
  r.settle
  checkEq "checkbox: click reports the new value" (← calls.get) #[true]
  check "checkbox: checked fill settles to primary" (near (← r.pixel 15 15) L.primary)
  -- Checkmark: onPrimary (white-ish) pixels inside the box.
  let surf ← (← r.ctx.sdlRenderer).readPixels
  let mut mark := 0
  for y in [13:28] do
    for x in [13:28] do
      let c ← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)
      if c.r > 220 && c.g > 220 && c.b > 220 then mark := mark + 1
  check s!"checkbox: checkmark glyphs present ({mark})" (mark > 0)
  -- Keyboard toggle (Space when focused).
  r.key .tab
  r.settle
  r.key .space
  r.settle
  checkEq "checkbox: Space toggles back" (← calls.get) #[true, false]
  -- Clear focus and hover first: their state layers legitimately tint the
  -- target (the pointer is still parked on it from the click).
  r.key .escape
  r.move 200 140
  r.settle
  check "checkbox: unchecked visuals return" (near (← r.pixel 15 15) .white)

/-- Radio pair: clicking the second selects it (animated dot appears there,
not on the first); Enter when focused also selects. -/
private def radioSelects : IO Unit := do
  let choice ← MutableState.create (0 : Nat)
  let calls ← IO.mkRef (#[] : Array Nat)
  let r ← mboot (h := 200) <| themed <| Column do
    Tests.restartable 1 do
      let sel ← choice.get
      RadioButton (sel == 0) (do calls.modify (·.push 0); choice.set 0)
      RadioButton (sel == 1) (do calls.modify (·.push 1); choice.set 1)
  r.settle
  check "radio: first selected dot is primary" (near (← r.pixel 20 20) L.primary)
  check "radio: second dot absent" (near (← r.pixel 20 60) .white)
  check "radio: second ring stroke present" (near (← r.pixel 20 51) L.onSurfaceVariant 30)
  r.click 20 60
  r.settle
  checkEq "radio: click reports the second" (← calls.get) #[1]
  check "radio: dot animates in on the second" (near (← r.pixel 20 60) L.primary)
  check "radio: dot leaves the first" (near (← r.pixel 20 20) .white)
  -- Tab reaches the first radio; Enter selects it again.
  r.key .tab
  r.settle
  r.key .return
  r.settle
  checkEq "radio: Enter selects the focused radio" (← calls.get) #[1, 0]

/-- Switch: click toggles (thumb slides right, track turns primary), Enter
toggles back. -/
private def switchToggles : IO Unit := do
  let on ← MutableState.create false
  let calls ← IO.mkRef (#[] : Array Bool)
  let r ← mboot <| themed <| Tests.restartable 1 do
    let o ← on.get
    Switch o (fun v => do calls.modify (·.push v); on.set v)
  check "switch: unchecked track is surfaceVariant" (near (← r.pixel 6 20) L.surfaceVariant)
  check "switch: unchecked thumb (outline) sits left" (near (← r.pixel 16 20) L.outline)
  r.click 26 20
  r.settle
  checkEq "switch: click reports on" (← calls.get) #[true]
  check "switch: track animates to primary" (near (← r.pixel 6 20) L.primary)
  check "switch: thumb slides right (onPrimary)" (near (← r.pixel 36 20) L.onPrimary)
  r.key .tab
  r.settle
  r.key .return
  r.settle
  checkEq "switch: Enter toggles back off" (← calls.get) #[true, false]
  check "switch: thumb returns left" (near (← r.pixel 16 20) L.outline)

/-- Disabled selection controls: published as disabled in semantics, and
they ignore mouse and keyboard entirely (MT framework — clicks find each
control's real bounds instead of hand-computed coordinates). -/
private def disabledControls : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let bump : IO Unit := calls.modify (· + 1)
  runComposeTest (height := 220)
    (Column do
      Checkbox false (fun _ => bump) (enabled := false)
        (modifier := Modifier.testTag "cb")
      Switch false (fun _ => bump) (enabled := false)
        (modifier := Modifier.testTag "sw")
      RadioButton false bump (enabled := false)
        (modifier := Modifier.testTag "rb")
      Slider 0.5 (fun _ => bump) (enabled := false)
        (modifier := Modifier.testTag "sl"))
    do
      assertDisabled (.tag "cb")
      assertDisabled (.tag "sw")
      assertDisabled (.tag "rb")
      assertDisabled (.tag "sl")
      click (.tag "cb")
      click (.tag "sw")
      click (.tag "rb")
      click (.tag "sl")
      pressKey .tab       -- nothing focusable
      pressKey .return
      pressKey .space
      pressKey .right
      checkEq "disabled: no callback fired by mouse or keyboard" (← calls.get) 0

/-! ## Slider -/

/-- Continuous slider: press-to-seek, drag with continuous updates then
`onValueChangeFinished`, arrow/Home/End keys, and track pixels. -/
private def sliderInteraction : IO Unit := do
  let value ← MutableState.create (0.2 : Float32)
  let changes ← IO.mkRef (#[] : Array Float32)
  let finished ← IO.mkRef (0 : Nat)
  let r ← mboot <| themed <| Tests.restartable 1 do
    let v ← value.get
    Slider v (fun x => do changes.modify (·.push x); value.set x)
      (onValueChangeFinished := finished.modify (· + 1))
  -- Track geometry: width 240, pad 12 ⇒ track 12..228 (216 px).
  -- Press-to-seek at the center.
  r.click 120 20
  r.settle
  let cs ← changes.get
  check s!"slider: center press seeks to ≈0.5 ({cs})"
    (cs.size == 1 && approx cs[0]! 0.5)
  checkEq "slider: release fires onValueChangeFinished" (← finished.get) 1
  -- Pixels at value 0.5: active left, thumb center, inactive right.
  check "slider: active track is primary" (near (← r.pixel 60 20) L.primary)
  check "slider: thumb is primary" (near (← r.pixel 120 20) L.primary)
  check "slider: inactive track is surfaceVariant" (near (← r.pixel 180 20) L.surfaceVariant)
  -- Drag: press at ¼, drag through ½ to ¾, release.
  changes.set #[]
  r.press 66 20
  r.move 120 20
  r.move 174 20
  r.release 174 20
  r.settle
  let ds ← changes.get
  check s!"slider: drag updates continuously ({ds})"
    (ds.size == 3 && approx ds[0]! 0.25 && approx ds[1]! 0.5 && approx ds[2]! 0.75)
  check "slider: drag values are nondecreasing"
    (ds.size < 2 || (ds.zip (ds.extract 1 ds.size)).all fun (a, b) => a ≤ b + 0.0001)
  checkEq "slider: drag end fires onValueChangeFinished once" (← finished.get) 2
  -- Keyboard: Tab focuses; arrows step 1 % of the range, Home/End jump.
  r.key .tab
  r.settle
  changes.set #[]
  r.key .right
  r.settle
  check "slider: Right steps up by 1%" (approx (← value.get) 0.76 0.001)
  -- Settled presses: one step each (the batched-repeat case is asserted at
  -- the end of this scenario).
  r.key .left
  r.settle
  r.key .left
  r.settle
  check "slider: Left steps down" (approx (← value.get) 0.74 0.001)
  r.key .home
  r.settle
  check "slider: Home jumps to the range start" ((← value.get) == 0.0)
  r.key .«end»
  r.settle
  check "slider: End jumps to the range end" ((← value.get) == 1.0)
  checkEq "slider: each key fires onValueChangeFinished" (← finished.get) 7
  -- Two key repeats in ONE frame drain (no settle between): each must step
  -- from the previously reported value via the optimistic ref (the
  -- TextField pattern) — 1.0 → 0.99 → 0.98 — not twice from the stale
  -- composition capture.
  r.key .left
  r.key .left
  r.settle
  check s!"slider: batched key repeats each take a step ({← value.get})"
    (approx (← value.get) 0.98 0.001)

/-- Stepped slider over a custom range: seeks snap to the tick grid and the
callback reports range-mapped values. -/
private def sliderStepsAndRange : IO Unit := do
  let value ← MutableState.create (0.0 : Float32)
  let changes ← IO.mkRef (#[] : Array Float32)
  let r ← mboot <| themed <| Tests.restartable 1 do
    let v ← value.get
    Slider v (fun x => do changes.modify (·.push x); value.set x)
      (valueRange := (0, 100)) (steps := 3)
  -- Grid: 0, 25, 50, 75, 100. x=98 ⇒ raw f≈0.40 ⇒ snaps to 0.5 ⇒ 50.
  r.click 98 20
  r.settle
  let cs ← changes.get
  check s!"slider steps: click snaps to the grid in range units ({cs})"
    (cs.size == 1 && approx cs[0]! 50 0.5)
  -- x=220 ⇒ raw f≈0.96 ⇒ snaps to 1 ⇒ 100.
  r.click 220 20
  r.settle
  check "slider steps: near-end click snaps to the max" (approx (← value.get) 100 0.5)
  -- Arrows step one tick (25).
  r.key .tab
  r.settle
  r.key .left
  r.settle
  check "slider steps: Left steps one tick down" (approx (← value.get) 75 0.5)
  r.key .right
  r.settle
  check "slider steps: Right steps one tick up (clamped at max)"
    (approx (← value.get) 100 0.5)

/-! ## Progress indicators -/

/-- Determinate indicators: the linear bar fills exactly its fraction; the
circular arc covers the swept half only. -/
private def determinateProgress : IO Unit := do
  let r ← mboot <| themed <| Column do
    LinearProgressIndicator (some 0.5)
    CircularProgressIndicator (some 0.5)
  -- Linear: 240 wide, 4 tall at y 0..4.
  check "linear 0.5: left half is primary" (near (← r.pixel 60 2) L.primary)
  check "linear 0.5: right half is the track" (near (← r.pixel 180 2) L.surfaceVariant)
  -- Circular below (40×40 at y 4..44): arc from the top, half a turn
  -- clockwise ⇒ covers the right side, leaves the left bare.
  check "circular 0.5: right of the ring is primary" (near (← r.pixel 38 24) L.primary)
  check "circular 0.5: left of the ring is bare" (near (← r.pixel 2 24) .white)

/-- Indeterminate indicators keep changing across ticked frames. -/
private def indeterminateProgress : IO Unit := do
  let r ← mboot <| themed <| Column do
    LinearProgressIndicator
    CircularProgressIndicator
  check "indeterminate: infinite transitions subscribed" (← r.s.hasFrameWork)
  -- Signature: which sample points read as primary (bar row + ring points).
  let signature : IO String := do
    let surf ← (← r.ctx.sdlRenderer).readPixels
    let mut sig := ""
    for i in [0:29] do
      let c ← surf.readPixel (Int32.ofNat (4 + i * 8)) 2
      sig := sig.push (if near c L.primary 40 then 'P' else '.')
    for i in [0:12] do
      let a := (i.toFloat32 / 12) * 2 * 3.14159265
      let x := 20 + 18 * (Float.cos a.toFloat).toFloat32
      let y := 24 + 18 * (Float.sin a.toFloat).toFloat32
      let c ← surf.readPixel x.toInt32 y.toInt32
      sig := sig.push (if near c L.primary 40 then 'P' else '.')
    return sig
  r.tick 100
  let s1 ← signature
  r.tick 300
  let s2 ← signature
  r.tick 300
  let s3 ← signature
  check s!"indeterminate: frames differ ({s1} → {s2})" (s1 != s2)
  check s!"indeterminate: and keep differing ({s2} → {s3})" (s2 != s3)
  check "indeterminate: something is drawn" (s2.any (· == 'P') || s3.any (· == 'P'))

/-! ## Surface shape -/

/-- A rounded Surface: pixels outside the corner radius show the background;
the interior and straight edges show the container. -/
private def surfaceShapePixels : IO Unit := do
  let r ← mboot <| themed <|
    Surface (modifier := Modifier.size 80 80) (shape := .rounded 16) (color := some L.primary)
  check "surface shape: interior is the container" (near (← r.pixel 40 40) L.primary)
  check "surface shape: straight edge is the container" (near (← r.pixel 2 40) L.primary)
  let corner ← r.pixel 2 2
  check s!"surface shape: corner outside the radius is background ({showColor corner})"
    (near corner .white)
  check "surface shape: opposite corner too" (near (← r.pixel 78 78) .white)

/-- The `.glass` surface material renders the translucent treatment
(`Compose.Material.Glass`): visibly different pixels from `.opaque` — the
default white tint wash over the white background instead of the container
role — while the content-color contract still resolves on the untinted
role. A `GlassSurface` records the full adaptive chain: shadow, masked
backdrop frost (a no-op on this SDL backend — the pixels stay Phase-A),
gradient tint, radial sheen, gradient rim, clip. -/
private def surfaceGlassMaterial : IO Unit := do
  -- An elevated, rounded, shadowed Surface — every arm of the background
  -- chain `backgroundModifier` builds.
  let scene (material : Option SurfaceMaterial) : Composable Unit :=
    themed <| Box (modifier := Modifier.fillMaxSize |>.background .white) <|
      Surface (modifier := Modifier.size 80 60) (shape := .rounded 12)
        (color := some L.primary) (elevation := 6) (material := material)
  let plainRig ← mboot (scene none)
  let glassRig ← mboot (scene (some (.glass {})))
  let plainShot ← (← plainRig.ctx.sdlRenderer).readPixels
  let glassShot ← (← glassRig.ctx.sdlRenderer).readPixels
  let mut diffs := 0
  for y in [0:53] do
    for x in [0:80] do
      let a ← plainShot.readPixel (Int32.ofNat (x * 3)) (Int32.ofNat (y * 3))
      let b ← glassShot.readPixel (Int32.ofNat (x * 3)) (Int32.ofNat (y * 3))
      unless a.r == b.r && a.g == b.g && a.b == b.b && a.a == b.a do
        diffs := diffs + 1
  check s!"glass: renders visibly differently from opaque ({diffs} pixels differ)"
    (diffs > 0)
  -- The glass interior is the translucent white wash over the backdrop
  -- (which includes the panel's own shadow — a translucent fill no longer
  -- covers the umbra) — a bright near-white, NOT the container role.
  let interior ← glassRig.pixel 40 30
  check s!"glass: interior is the light tint wash, not the container role \
           ({interior.r},{interior.g},{interior.b})"
    (interior.r.toNat ≥ 200 && interior.g.toNat ≥ 200 && interior.b.toNat ≥ 200
      && !near interior L.primary 12)
  -- Content color is unaffected: translucency is a rendering treatment, not
  -- a role change.
  let root ← LayoutNode.create
  let cap ← IO.mkRef (none : Option (Compose.Color × Compose.Color))
  let _ ← Composition.create (LayoutNode.applier root) <| MaterialTheme do
    Surface (color := some L.primary) (material := some (.glass {})) do
      cap.set (some (← LocalContentColor.current, (← LocalTextStyle.current).color))
  let some (cc, tc) ← cap.get | throw (IO.userError "glass capture missing")
  check "glass: content color still the untinted role pair" (cc == L.onPrimary)
  check "glass: text style recolored to it too" (tc == L.onPrimary)
  -- GlassSurface: content color defaults to onSurface, and the recorded
  -- chain is shadow → gradient tint → radial sheen → gradient rim (the
  -- light adaptive spec) with the content clipped to the shape.
  let gcap ← IO.mkRef (none : Option Compose.Color)
  let gRig ← mboot <| themed <|
    Box (modifier := Modifier.fillMaxSize |>.background .white) <|
      GlassSurface (modifier := Modifier.size 80 60) (shape := .rounded 12) do
        gcap.set (some (← LocalContentColor.current))
  check "glass surface: content color defaults to onSurface"
    ((← gcap.get) == some L.onSurface)
  let (list, _) ← Compose.Draw.DrawScope.record {} gRig.ctx.root.drawTree
  let briefs := (list.map (·.brief)).toList
  check "glass surface: records the elevation shadow"
    (briefs.any fun b => (b.splitOn "rrShadow").length > 1)
  check "glass surface: records the shape-masked backdrop frost at σ = blurRadius/2"
    (briefs.any fun b => b.startsWith "backdrop "
      && (b.splitOn "rounded=").length > 1 && (b.splitOn "sigma=24").length > 1)
  check "glass surface: the default spec's refractive edge bend rides the prim"
    (briefs.any fun b => b.startsWith "backdrop " && (b.splitOn " refr=").length > 1)
  check "glass surface: records the vertical gradient tint"
    (briefs.any fun b => (b.splitOn "rrFill").length > 1 && (b.splitOn "grad[2]").length > 1)
  check "glass surface: records the radial sheen"
    (briefs.any fun b => (b.splitOn "rrFill").length > 1 && (b.splitOn "radial[2]").length > 1)
  check "glass surface: records the gradient rim stroke"
    (briefs.any fun b => (b.splitOn "rrStroke").length > 1 && (b.splitOn "grad[2]").length > 1)

/-- Themed `ThemeTokens` reach the widgets: a distinctive
`interactions.disabledContentAlpha` changes the content color a disabled
widget establishes, and the elevation scale changes what an elevated widget
asks `Modifier.shadow` for. -/
private def themedTokensFlow : IO Unit := do
  -- A disabled TextButton resolves its label color through
  -- `tokens.interactions.disabledContentAlpha`; capture it from the slot.
  let capture (tokens : Option ThemeTokens) : IO Compose.Color := do
    let cap ← IO.mkRef (none : Option Compose.Color)
    let _ ← mboot <| MaterialTheme (tokens := tokens) <|
      TextButton (pure ()) (enabled := false) do
        cap.set (some (← LocalContentColor.current))
    let some c ← cap.get | throw (IO.userError "disabled-content capture missing")
    return c
  let dflt ← capture none
  let themedAlpha ← capture (some { interactions := { disabledContentAlpha := 0.9 } })
  check "tokens: default disabled content alpha is the baseline token"
    (dflt == L.onSurface.withAlpha disabledContentAlpha)
  check s!"tokens: themed disabled content alpha reaches the widget"
    (themedAlpha == L.onSurface.withAlpha 0.9)
  check "tokens: and it actually differs from the default" (themedAlpha != dflt)
  -- `ElevatedCard` reads `tokens.elevations.card`: a distinctive value lands
  -- in the recorded shadow spec.
  let shadowBrief (tokens : Option ThemeTokens) : IO String := do
    let r ← mboot <| MaterialTheme (tokens := tokens) <|
      ElevatedCard (modifier := Modifier.size 60 40)
    let density ← r.ctx.density
    let (list, _) ← Compose.Draw.DrawScope.record density r.ctx.root.drawTree
    let briefs := (list.map (·.brief)).toList.filter fun b =>
      (b.splitOn "rrShadow").length > 1
    return String.intercalate "|" briefs
  let dfltShadow ← shadowBrief none
  let themedShadow ← shadowBrief (some { elevations := { card := 11 } })
  check s!"tokens: default card elevation records the baseline shadow ({dfltShadow})"
    ((dfltShadow.splitOn s!"blur={Draw.fmtF 1}").length > 1)
  check s!"tokens: themed card elevation reaches Modifier.shadow ({themedShadow})"
    ((themedShadow.splitOn s!"blur={Draw.fmtF 11}").length > 1)

/-- The Material group. -/
def run : IO Unit := do
  themeLocals
  themeBundle
  surfaceContentColor
  surfaceShapePixels
  surfaceGlassMaterial
  themedTokensFlow
  buttonBasics
  buttonHoverLayer
  buttonPressRipple
  buttonDisabled
  checkboxToggles
  radioSelects
  switchToggles
  disabledControls
  sliderInteraction
  sliderStepsAndRange
  determinateProgress
  indeterminateProgress

end Tests.Material
