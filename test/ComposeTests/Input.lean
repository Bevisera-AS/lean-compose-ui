import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Input test group (`test/ComposeTests/Input.lean`)

M6's synthetic-event suites, driven at two layers:

* **Router layer** (no window): real compositions on the `LayoutNode` applier
  with a fake-clock scheduler (`LocalScheduler` provider — the M5 pattern),
  measured directly, with `PointerEvent`/`KeyEvent`s injected through an
  `InputManager` whose `CursorSetter` records. Covers hit paths (z-order,
  clip bounds, wrapper offsets), consumption, hover diffing + cursors,
  gesture detectors (incl. scheduler-driven long press — no real sleeping),
  focus traversal/routing, `clickable`, and the `pointerInput` coroutine
  lifecycle.

* **Translator layer**: a bootstrapped headless window with constructed
  `Sdl.Event`s through `dispatchEvent` → `inputSink`, covering the SDL →
  `PointerEvent`/`KeyEvent` translation (coordinates, wheel delta
  pass-through, key/text routing, window-leave, the M11 text-client hook).
-/

namespace Tests.Input
open Compose Tests.Harness

instance : ToString Offset := ⟨fun o => s!"({o.x}, {o.y})"⟩

/-- Milliseconds → the scheduler's nanosecond clock. -/
private def ms (n : UInt64) : UInt64 := n * 1_000_000

/-- A scheduler over a settable fake clock. -/
private def fakeSched : IO (Scheduler × IO.Ref UInt64) := do
  let clock ← IO.mkRef (0 : UInt64)
  let s ← Scheduler.create (clock := clock.get)
  return (s, clock)

/-- Advance the fake clock and run everything due. -/
private def advance (s : Scheduler) (clock : IO.Ref UInt64) (toNs : UInt64) : IO Unit := do
  clock.set toNs
  s.runDue toNs

/-- A leaf `Layout` (no children, sized by its modifier). -/
private def leaf (m : Modifier) : Composable Unit := Layout m .leaf

/-- A composition + input manager rig over a fake-clock scheduler: composes
`content` on a fresh root, measures it, records cursor changes, and starts
the pointer coroutines (`runDue`). -/
private structure Rig where
  s : Scheduler
  clock : IO.Ref UInt64
  root : LayoutNode
  comp : Composition
  im : InputManager
  cursors : IO.Ref (Array Sdl.SystemCursor)

private def rig (content : Composable Unit) (w : Int32 := 200) (h : Int32 := 200) : IO Rig := do
  let (s, clock) ← fakeSched
  let root ← LayoutNode.create
  let comp ← Composition.create (LayoutNode.applier root)
    (CompositionLocalProvider LocalScheduler (some s) content)
  let _ ← root.remeasure { maxWidth := w, maxHeight := h }
  let cursors ← IO.mkRef (#[] : Array Sdl.SystemCursor)
  let im ← InputManager.create root { set := fun c => cursors.modify (·.push c) }
    (sched := some s)
  s.runDue 0
  return { s, clock, root, comp, im, cursors }

/-- Recompose (drain) and restart any relaunched pointer coroutines. -/
private def Rig.settle (r : Rig) : IO Unit := do
  r.comp.drain
  let _ ← r.root.remeasure { maxWidth := 200, maxHeight := 200 }
  r.s.runDue (← r.clock.get)

/-! ## Synthetic pointer events -/

private def pressAt (x y : Float32) (clicks : UInt8 := 1) : PointerEvent :=
  { eventType := .press, position := ⟨x, y⟩, button := some .left, clicks }

private def releaseAt (x y : Float32) (clicks : UInt8 := 1) : PointerEvent :=
  { eventType := .release, position := ⟨x, y⟩, button := some .left, clicks }

private def moveTo (x y : Float32) : PointerEvent :=
  { eventType := .move, position := ⟨x, y⟩ }

private def scrollAt (x y : Float32) (delta : Offset) : PointerEvent :=
  { eventType := .scroll, position := ⟨x, y⟩, scrollDelta := delta }

private def kindName : PointerEventType → String
  | .press => "press"
  | .release => "release"
  | .move => "move"
  | .scroll => "scroll"
  | .enter => "enter"
  | .exit => "exit"
  | .pinch => "pinch"

/-- Event-logging `pointerInput` handler: logs events of the given types
(empty = all), optionally with the local position, consuming the types in
`consume`. -/
private partial def logEvents (log : IO.Ref (Array String)) (tag : String)
    (only : List PointerEventType := []) (consume : List PointerEventType := [])
    (withPos : Bool := false) (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if consume.contains ev.eventType then ev.consume
  if only.isEmpty || only.contains ev.eventType then
    let pos := if withPos then s!"@{ev.position.x.toInt32},{ev.position.y.toInt32}" else ""
    log.modify (·.push s!"{tag}:{kindName ev.eventType}{pos}")
  logEvents log tag only consume withPos scope

/-! ## Hit paths -/

/-- Later siblings sit on top: only the topmost hit subtree receives events;
a point missing the top sibling falls through to the one below. -/
private def hitZOrder : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1 (logEvents log "under" (only := [.press])))
    leaf (Modifier.size 30 30 |>.pointerInput 2 (logEvents log "over" (only := [.press])))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  checkEq "z-order: overlap goes to the later sibling" (← log.get) #["over:press"]
  log.set #[]
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  let _ ← r.im.pointerEvent (pressAt 40 40)
  checkEq "z-order: point past the top sibling falls through"
    (← log.get) #["under:press"]

/-- A `Modifier.clip`ped region only hits inside the shape (geometric circle
test), for the node's own handlers and for its children. -/
private def hitClipBounds : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Box do
    Box (modifier := Modifier.size 40 40 |>.clip .circle |>.pointerInput 1 (logEvents log "self")) do
      leaf (Modifier.fillMaxSize |>.pointerInput 2 (logEvents log "child"))
    pure ()
  let _ ← r.im.pointerEvent (pressAt 2 2)   -- inside the rect, outside the circle
  checkEq "clip: circle corner misses" (← log.get) (#[] : Array String)
  let _ ← r.im.pointerEvent (releaseAt 2 2)
  let _ ← r.im.pointerEvent (pressAt 20 20) -- circle center
  checkEq "clip: circle center hits child then self (leaf→root)"
    (← log.get) #["child:press", "self:press"]

/-- A pointer element after `padding` covers only the padded-inner wrapper;
positions are delivered element-local. -/
private def hitWrapperOffsets : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Box do
    leaf (Modifier.padding (all := 10)
      |>.pointerInput 1 (logEvents log "pad" (withPos := true))
      |>.size 30 30)
  let _ ← r.im.pointerEvent (pressAt 5 5)   -- in the padding ring
  checkEq "offset: padding ring misses" (← log.get) (#[] : Array String)
  let _ ← r.im.pointerEvent (releaseAt 5 5)
  let _ ← r.im.pointerEvent (pressAt 15 18)
  checkEq "offset: inner region hits with local coordinates"
    (← log.get) #["pad:press@5,8"]

/-! ## Consumption -/

/-- Inner (leaf) handlers run first; consuming stops outer delivery,
unconsumed events bubble to the root. -/
private def consumptionBubbling : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <|
    Box (modifier := Modifier.size 50 50 |>.pointerInput 1
          (logEvents log "outer" (only := [.press, .release]))) do
      leaf (Modifier.size 50 50 |>.pointerInput 2
        (logEvents log "inner" (only := [.press, .release]) (consume := [.press])))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  checkEq "consume: inner consumed, outer silent" (← log.get) #["inner:press"]
  log.set #[]
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  checkEq "consume: unconsumed release bubbles leaf→root"
    (← log.get) #["inner:release", "outer:release"]

/-- `Modifier.onScroll` consumption: an inner handler eating the full delta
silences the outer one; `.zero` lets the event through untouched. -/
private def scrollConsumption : IO Unit := do
  let inner ← IO.mkRef (#[] : Array Offset)
  let outer ← IO.mkRef (#[] : Array Offset)
  let eat ← IO.mkRef true
  let r ← rig <|
    Box (modifier := Modifier.size 50 50 |>.onScroll (fun d => do outer.modify (·.push d); pure .zero)) do
      leaf (Modifier.size 50 50 |>.onScroll (fun d => do
        inner.modify (·.push d)
        return (if ← eat.get then d else .zero)))
  let _ ← r.im.pointerEvent (scrollAt 10 10 ⟨0, 3⟩)
  checkEq "scroll: inner handler got the delta" (← inner.get) #[(⟨0, 3⟩ : Offset)]
  checkEq "scroll: consumed, outer silent" (← outer.get) (#[] : Array Offset)
  eat.set false
  let _ ← r.im.pointerEvent (scrollAt 10 10 ⟨0, -2⟩)
  checkEq "scroll: unconsumed bubbles to the outer handler"
    (← outer.get) #[(⟨0, -2⟩ : Offset)]

/-- Per-axis wheel splitting: an inner vertical-only consumer leaves the
horizontal remainder of a diagonal event to the outer handler; a fully
consumed event stops before it. -/
private def scrollAxisSplit : IO Unit := do
  let outer ← IO.mkRef (#[] : Array Offset)
  let r ← rig <|
    Box (modifier := Modifier.size 50 50 |>.onScroll (fun d => do outer.modify (·.push d); pure d)) do
      leaf (Modifier.size 50 50 |>.onScroll (fun d => pure ⟨0, d.y⟩))
  let _ ← r.im.pointerEvent (scrollAt 10 10 ⟨4, 3⟩)
  checkEq "axis split: inner ate y, outer saw the x remainder"
    (← outer.get) #[(⟨4, 0⟩ : Offset)]
  let _ ← r.im.pointerEvent (scrollAt 10 10 ⟨0, 5⟩)
  checkEq "axis split: a fully consumed event stops inside" ((← outer.get).size) 1

/-! ## Hover and cursor -/

/-- Hover diffing across two siblings and their common parent: enter/exit
fire on the diff only (parent stays hovered while crossing children), and
leaving everything exits leaf→root. -/
private def hoverEnterExit : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let ee : List PointerEventType := [.enter, .exit]
  let r ← rig <|
    Box (modifier := Modifier.size 100 80 |>.pointerInput 9 (logEvents log "p" ee)) do
      Row do
        leaf (Modifier.size 50 50 |>.pointerInput 1 (logEvents log "a" ee))
        leaf (Modifier.size 50 50 |>.pointerInput 2 (logEvents log "b" ee))
  let _ ← r.im.pointerEvent (moveTo 10 10)
  checkEq "hover: enters root→leaf" (← log.get) #["p:enter", "a:enter"]
  log.set #[]
  let _ ← r.im.pointerEvent (moveTo 60 10)
  checkEq "hover: crossing siblings exits a, enters b, parent stays"
    (← log.get) #["a:exit", "b:enter"]
  log.set #[]
  let _ ← r.im.pointerEvent (moveTo 150 150)
  checkEq "hover: leaving all exits leaf→root" (← log.get) #["b:exit", "p:exit"]

/-- The leaf-most hovered `pointerHoverIcon` wins; the default is restored
where none applies. -/
private def hoverCursor : IO Unit := do
  let r ← rig <|
    Box (modifier := Modifier.size 100 80 |>.pointerHoverIcon .crosshair) do
      Row do
        leaf (Modifier.size 50 50 |>.pointerHoverIcon .text)
        leaf (Modifier.size 50 50)
  let _ ← r.im.pointerEvent (moveTo 10 10)   -- over the text leaf
  let _ ← r.im.pointerEvent (moveTo 60 10)   -- over the plain leaf: parent icon
  let _ ← r.im.pointerEvent (moveTo 10 70)   -- over the parent only
  let _ ← r.im.pointerEvent (moveTo 150 150) -- off everything
  checkEq "cursor: topmost icon wins, default restored (dedup on no change)"
    ((← r.cursors.get).map (·.val)) (#[.text, .crosshair, .default].map
      (Sdl.SystemCursor.val))

/-! ## Gestures -/

/-- Tap: press+release in bounds fires once; release outside (captured path)
is a click-cancel. -/
private def tapGesture : IO Unit := do
  let taps ← IO.mkRef (#[] : Array (Int32 × Int32))
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures (onTap := some fun p => taps.modify (·.push (p.x.toInt32, p.y.toInt32)))))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  checkEq "tap: nothing until release" (← taps.get) (#[] : Array (Int32 × Int32))
  let _ ← r.im.pointerEvent (releaseAt 12 14)
  checkEq "tap: press+release fires with the release position" (← taps.get) #[((12 : Int32), (14 : Int32))]
  -- Click-cancel: drag off the node before releasing.
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 120 120)
  let _ ← r.im.pointerEvent (releaseAt 120 120)
  checkEq "tap: release outside bounds cancels" ((← taps.get).size) 1

/-- Double click via SDL's clicks counter: the second press/release pair
(clicks = 2) fires `onDoubleTap` instead of `onTap`. -/
private def doubleTapGesture : IO Unit := do
  let taps ← IO.mkRef (0 : Nat)
  let doubles ← IO.mkRef (0 : Nat)
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onDoubleTap := some fun _ => doubles.modify (· + 1))))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  let _ ← r.im.pointerEvent (pressAt 10 10 (clicks := 2))
  let _ ← r.im.pointerEvent (releaseAt 10 10 (clicks := 2))
  checkEq "double: first click taps (no delay — documented deviation)" (← taps.get) 1
  checkEq "double: clicks=2 fires onDoubleTap" (← doubles.get) 1

/-- Secondary tap: a right-button press+release inside bounds fires
`onSecondaryTap` (never `onTap`); a release outside cancels; left clicks
still tap. -/
private def secondaryTapGesture : IO Unit := do
  let taps ← IO.mkRef (0 : Nat)
  let secs ← IO.mkRef (#[] : Array (Int32 × Int32))
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onSecondaryTap := some fun p => secs.modify (·.push (p.x.toInt32, p.y.toInt32)))))
  let rightAt := fun (t : PointerEventType) (x y : Float32) =>
    ({ eventType := t, position := ⟨x, y⟩, button := some .right } : PointerEvent)
  let _ ← r.im.pointerEvent (rightAt .press 15 20)
  let _ ← r.im.pointerEvent (rightAt .release 15 20)
  checkEq "secondary: right click fires with the release position"
    (← secs.get) #[((15 : Int32), (20 : Int32))]
  checkEq "secondary: onTap stays silent" (← taps.get) 0
  -- Click-cancel: release outside the element.
  let _ ← r.im.pointerEvent (rightAt .press 15 20)
  let _ ← r.im.pointerEvent (moveTo 120 120)
  let _ ← r.im.pointerEvent (rightAt .release 120 120)
  checkEq "secondary: release outside cancels" ((← secs.get).size) 1
  -- The detector loops back to primary taps.
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  checkEq "secondary: left click still taps" (← taps.get) 1

/-- Long press: fires from the scheduler clock without a release, suppresses
the tap, and lets an `onPress`'s `tryAwaitRelease` return `false` (pressed
state resets). No real sleeping — the fake clock drives it. -/
private def longPressGesture : IO Unit := do
  let taps ← IO.mkRef (0 : Nat)
  let longs ← IO.mkRef (#[] : Array (Int32 × Int32))
  let pressed ← IO.mkRef (#[] : Array Bool)
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onLongPress := some fun p => longs.modify (·.push (p.x.toInt32, p.y.toInt32)))
        (onPress := some fun ps => do
          pressed.modify (·.push true)
          let ok ← ps.tryAwaitRelease
          pressed.modify (·.push ok))))
  let _ ← r.im.pointerEvent (pressAt 20 20)
  checkEq "long: nothing before the timeout" (← longs.get) (#[] : Array (Int32 × Int32))
  advance r.s r.clock (ms 600)
  checkEq "long: fires from the clock without a release" (← longs.get) #[((20 : Int32), (20 : Int32))]
  checkEq "long: tryAwaitRelease reported cancel" (← pressed.get) #[true, false]
  let _ ← r.im.pointerEvent (releaseAt 20 20)
  checkEq "long: the late release does not tap" (← taps.get) 0
  -- A quick click afterwards still taps (the loop recovered).
  let _ ← r.im.pointerEvent (pressAt 5 5)
  let _ ← r.im.pointerEvent (releaseAt 5 5)
  checkEq "long: detector loops back to taps" (← taps.get) 1

/-- Drag: 4 px start threshold, per-move deltas, end on release, cancel on
window leave. -/
private def dragGesture : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Box do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectDragGestures
        (onDrag := fun p d =>
          log.modify (·.push s!"drag@{p.x.toInt32},{p.y.toInt32}Δ{d.x.toInt32},{d.y.toInt32}"))
        (onDragStart := fun p => log.modify (·.push s!"start@{p.x.toInt32},{p.y.toInt32}"))
        (onDragEnd := log.modify (·.push "end"))
        (onDragCancel := log.modify (·.push "cancel"))))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 12 12)   -- ≈2.8 px, below the slop
  checkEq "drag: below the threshold nothing starts" (← log.get) (#[] : Array String)
  let _ ← r.im.pointerEvent (moveTo 20 20)   -- past the slop
  let _ ← r.im.pointerEvent (moveTo 25 20)
  let _ ← r.im.pointerEvent (moveTo 80 90)   -- outside the node: capture keeps delivering
  let _ ← r.im.pointerEvent (releaseAt 80 90)
  checkEq "drag: start/deltas/end sequence" (← log.get)
    #["start@20,20", "drag@20,20Δ10,10", "drag@25,20Δ5,0", "drag@80,90Δ55,70", "end"]
  log.set #[]
  -- Cancel: pointer leaves the window mid-drag.
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 30 10)
  let _ ← r.im.pointerEvent { eventType := .exit, position := ⟨30, 10⟩ }
  checkEq "drag: window leave cancels" (← log.get)
    #["start@30,10", "drag@30,10Δ20,0", "cancel"]
  -- A release within the slop is not a drag.
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 11 11)
  let _ ← r.im.pointerEvent (releaseAt 11 11)
  checkEq "drag: sub-slop click fires nothing" ((← log.get).size) 3
  log.set #[]
  -- A second button pressed mid-drag (even off the node) keeps the capture.
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 80 90)
  let _ ← r.im.pointerEvent { eventType := .press, position := ⟨80, 90⟩
                              button := some .right, clicks := 1 }
  let _ ← r.im.pointerEvent (moveTo 85 90)
  let _ ← r.im.pointerEvent (releaseAt 85 90)  -- left up ends the drag
  let _ ← r.im.pointerEvent { eventType := .release, position := ⟨85, 90⟩
                              button := some .right, clicks := 1 }
  checkEq "drag: second button mid-drag keeps the capture" (← log.get)
    #["start@80,90", "drag@80,90Δ70,80", "drag@85,90Δ5,0", "end"]

/-! ## Focus -/

/-- Tab order over three focusables (preorder = layout order), wrap-around,
Shift-Tab back, click-to-focus, press-on-nothing and Esc clear. -/
private def focusTraversal : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let fc (tag : String) : Bool → IO Unit := fun b =>
    log.modify (·.push s!"{tag}{if b then "+" else "-"}")
  let r ← rig <| Column do
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "a"))
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "b"))
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "c"))
  let tab (shift : Bool := false) : IO Bool :=
    r.im.keyEvent { key := .tab, mods := if shift then .lShift else .none }
  check "focus: tab handled" (← tab)
  checkEq "focus: tab lands on the first focusable" (← log.get) #["a+"]
  let _ ← tab
  let _ ← tab
  checkEq "focus: tab walks layout order (old loses before new gains)"
    (← log.get) #["a+", "a-", "b+", "b-", "c+"]
  let _ ← tab
  checkEq "focus: tab wraps to the first" (← log.get)
    #["a+", "a-", "b+", "b-", "c+", "c-", "a+"]
  let _ ← tab (shift := true)
  checkEq "focus: shift-tab goes back (wrapping)" ((← log.get).drop 7) #["a-", "c+"]
  log.set #[]
  -- Click-to-focus: press on the second leaf (Column stacks them at y 20..40).
  let _ ← r.im.pointerEvent (pressAt 10 30)
  let _ ← r.im.pointerEvent (releaseAt 10 30)
  checkEq "focus: click focuses the pressed focusable" (← log.get) #["c-", "b+"]
  log.set #[]
  -- Press on nothing clears.
  let _ ← r.im.pointerEvent (pressAt 150 150)
  let _ ← r.im.pointerEvent (releaseAt 150 150)
  checkEq "focus: press on nothing clears" (← log.get) #["b-"]
  -- Esc with nothing focused is unhandled; focused, it clears.
  check "focus: esc without focus falls through" (!(← r.im.keyEvent { key := .escape }))
  let _ ← tab
  log.set #[]
  check "focus: esc handled when focused" (← r.im.keyEvent { key := .escape })
  checkEq "focus: esc cleared" (← log.get) #["a-"]

/-- Key routing: the focused node's handlers first (consuming stops), then
ancestors, then the Tab fallback (which still traverses when the focused
node does not consume Tab, and is blocked when it does). -/
private def keyRouting : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let handler (tag : String) (eats : List Sdl.Keycode) : KeyEvent → IO Bool := fun ke => do
    if ke.down then log.modify (·.push s!"{tag}:{ke.key.val}")
    pure (eats.contains ke.key)
  let r ← rig <|
    Box (modifier := Modifier.size 100 100 |>.onKeyEvent (handler "anc" [])) do
      leaf (Modifier.size 20 20 |>.focusable |>.onKeyEvent (handler "leaf" [.a, .f]))
      leaf (Modifier.size 20 20 |>.focusable |>.onKeyEvent (handler "leaf2" [.tab]))
  check "route: unfocused key falls through" (!(← r.im.keyEvent { key := .a }))
  checkEq "route: no handlers ran unfocused" (← log.get) (#[] : Array String)
  let _ ← r.im.keyEvent { key := .tab }   -- focus the first leaf
  log.set #[]
  check "route: focused node consumes" (← r.im.keyEvent { key := .a })
  checkEq "route: consumed at the leaf, ancestor silent" (← log.get) #[s!"leaf:{Sdl.Keycode.a.val}"]
  log.set #[]
  check "route: unconsumed key reaches the ancestor chain" (!(← r.im.keyEvent { key := .b }))
  checkEq "route: leaf then ancestor" (← log.get)
    #[s!"leaf:{Sdl.Keycode.b.val}", s!"anc:{Sdl.Keycode.b.val}"]
  -- Tab not consumed by the first leaf → fallback traverses to the second.
  check "route: tab fallback traverses" (← r.im.keyEvent { key := .tab })
  check "route: second leaf focused" (← r.im.focus.isFocused (← (← r.root.child 0).child 1))
  -- The second leaf consumes Tab → traversal blocked.
  check "route: consumed tab is not a fallback" (← r.im.keyEvent { key := .tab })
  check "route: focus unchanged when tab is consumed"
    (← r.im.focus.isFocused (← (← r.root.child 0).child 1))

/-- Text input routes to the focused node's `onTextInput` (innermost first,
consuming stops). -/
private def textRouting : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Column do
    leaf (Modifier.size 20 20 |>.focusable
      |>.onTextInput (fun t => do log.modify (·.push s!"a:{t}"); pure true))
    leaf (Modifier.size 20 20 |>.focusable
      |>.onTextInput (fun t => do log.modify (·.push s!"b:{t}"); pure true))
  check "text: nothing focused, unhandled" (!(← r.im.textInput "x"))
  let _ ← r.im.keyEvent { key := .tab }
  check "text: focused node handles" (← r.im.textInput "hi")
  checkEq "text: delivered to the focused node only" (← log.get) #["a:hi"]

/-- A modal scope popping back to a node that was removed while the modal was
open clears focus instead of restoring the detached node. -/
private def modalPopDetached : IO Unit := do
  let show' ← MutableState.create true
  let r ← rig <| Tests.restartable 1 do
    if ← show'.get then
      withGroup 11 <| Column do
        leaf (Modifier.size 20 20 |>.focusable)
    else
      withGroup 12 (pure ())
  let _ ← r.im.keyEvent { key := .tab }   -- focus the leaf
  check "modal-pop: leaf focused" ((← r.im.focus.focused).isSome)
  r.im.focus.pushModalScope 7
  check "modal-pop: push saved and cleared" ((← r.im.focus.focused).isNone)
  show'.set false
  r.settle
  r.im.focus.popModalScope 7
  check "modal-pop: pop to a removed node clears instead of restoring"
    ((← r.im.focus.focused).isNone)

/-! ## clickable -/

/-- `Modifier.clickable`: mouse click fires, Enter/Space fire when focused,
disabled does nothing, and the interaction flags are observable while held /
hovered. -/
private def clickableBehavior : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let r ← rig <| Box do
    let src ← rememberInteractionSource
    SideEffect (srcCell.set (some src))
    leaf (Modifier.size 40 40 |>.clickable (clicks.modify (· + 1)) (source := some src))
  let some src ← srcCell.get | throw (IO.userError "interaction source not captured")
  -- Mouse click + pressed interaction during the hold.
  check "clickable: not pressed initially" (!(← src.pressed.get))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  check "clickable: pressed while held" (← src.pressed.get)
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  check "clickable: released resets pressed" (!(← src.pressed.get))
  checkEq "clickable: mouse click fires" (← clicks.get) 1
  -- Hover interaction + pointer cursor.
  let _ ← r.im.pointerEvent (moveTo 10 10)
  check "clickable: hovered while over" (← src.hovered.get)
  checkEq "clickable: hand cursor" ((← r.cursors.get).map (·.val)) #[Sdl.SystemCursor.pointer.val]
  let _ ← r.im.pointerEvent (moveTo 150 150)
  check "clickable: hover exits" (!(← src.hovered.get))
  -- Keyboard activation when focused.
  let _ ← r.im.keyEvent { key := .tab }
  check "clickable: focus interaction" (← src.focused.get)
  check "clickable: Enter activates" (← r.im.keyEvent { key := .return })
  check "clickable: Space activates" (← r.im.keyEvent { key := .space })
  checkEq "clickable: keyboard clicks fired" (← clicks.get) 3
  check "clickable: repeat does not activate"
    (!(← r.im.keyEvent { key := .return, isRepeat := true }))
  checkEq "clickable: repeat fired nothing" (← clicks.get) 3

/-- Disabled `clickable`: no clicks, no focus, no keyboard activation. -/
private def clickableDisabled : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let r ← rig <| Box do
    leaf (Modifier.size 40 40 |>.clickable (clicks.modify (· + 1)) (enabled := false))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  checkEq "clickable: disabled ignores the mouse" (← clicks.get) 0
  let _ ← r.im.keyEvent { key := .tab }
  check "clickable: disabled is not focusable" ((← r.im.focus.focused).isNone)
  let _ ← r.im.keyEvent { key := .return }
  checkEq "clickable: disabled ignores the keyboard" (← clicks.get) 0

/-- Cancelling `clickable`'s gesture coroutine mid-press (here: the `enabled`
flip relaunch path) resets the pressed interaction instead of latching the
state layer on. -/
private def clickableCancelResetsPressed : IO Unit := do
  let enabled ← MutableState.create true
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let r ← rig <| Tests.restartable 1 <| Box do
    let src ← rememberInteractionSource
    SideEffect (srcCell.set (some src))
    leaf (Modifier.size 40 40
      |>.clickable (pure ()) (enabled := (← enabled.get)) (source := some src))
  let some src ← srcCell.get | throw (IO.userError "interaction source not captured")
  let _ ← r.im.pointerEvent (pressAt 10 10)
  check "press-cancel: pressed while held" (← src.pressed.get)
  enabled.set false
  r.settle
  check "press-cancel: relaunch mid-press resets pressed" (!(← src.pressed.get))

open Compose.Test in
/-- MT-level: hold a real press through the full pipeline, flip `enabled`
mid-press, and the interaction source resets. -/
private def clickableCancelMt : IO Unit := do
  let enabled ← MutableState.create true
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  runComposeTest
    (Tests.restartable 1 do
      let src ← rememberInteractionSource
      SideEffect (srcCell.set (some src))
      Box (modifier := Modifier.testTag "hold" |>.size 60 30
        |>.clickable (pure ()) (enabled := (← enabled.get)) (source := some src))) do
      let some src ← srcCell.get | throw (IO.userError "interaction source not captured")
      mouseDown (← boundsOf (.tag "hold")).center
      check "press-cancel MT: pressed while held" (← src.pressed.get)
      enabled.set false
      awaitIdle
      check "press-cancel MT: enabled flip mid-press resets pressed"
        (!(← src.pressed.get))

/-! ## Multi-pointer (touch) -/

private def fingerPress (pid : UInt64) (x y : Float32) : PointerEvent :=
  { eventType := .press, position := ⟨x, y⟩, pointerId := pid
    button := some .left, clicks := 1 }

private def fingerRelease (pid : UInt64) (x y : Float32) : PointerEvent :=
  { eventType := .release, position := ⟨x, y⟩, pointerId := pid
    button := some .left, clicks := 1 }

private def fingerCancel (pid : UInt64) (x y : Float32) : PointerEvent :=
  { eventType := .exit, position := ⟨x, y⟩, pointerId := pid }

private def fingerMove (pid : UInt64) (x y : Float32) : PointerEvent :=
  { eventType := .move, position := ⟨x, y⟩, pointerId := pid }

/-- Two fingers on two clickables run independent gestures: the second press
hit-tests its own target (not the first finger's captured path), both are
pressed at once, and each release fires its own click. -/
private def multiTouchIndependentPresses : IO Unit := do
  let aClicks ← IO.mkRef (0 : Nat)
  let bClicks ← IO.mkRef (0 : Nat)
  let srcs ← IO.mkRef (#[] : Array InteractionSource)
  let r ← rig <| Row do
    let srcA ← rememberInteractionSource
    let srcB ← rememberInteractionSource
    SideEffect (srcs.set #[srcA, srcB])
    leaf (Modifier.size 40 40 |>.clickable (aClicks.modify (· + 1)) (source := some srcA))
    leaf (Modifier.size 40 40 |>.clickable (bClicks.modify (· + 1)) (source := some srcB))
  let #[srcA, srcB] ← srcs.get | throw (IO.userError "interaction sources not captured")
  let _ ← r.im.pointerEvent (fingerPress 1 10 10)   -- finger 1 on A
  let _ ← r.im.pointerEvent (fingerPress 2 50 10)   -- finger 2 on B, mid-gesture
  check "two fingers: A pressed" (← srcA.pressed.get)
  check "two fingers: B pressed at the same time" (← srcB.pressed.get)
  let _ ← r.im.pointerEvent (fingerRelease 1 10 10)
  check "two fingers: releasing A leaves B held" (← srcB.pressed.get)
  check "two fingers: A released" (!(← srcA.pressed.get))
  let _ ← r.im.pointerEvent (fingerRelease 2 50 10)
  checkEq "two fingers: A clicked once" (← aClicks.get) 1
  checkEq "two fingers: B clicked once" (← bClicks.get) 1

/-- A finger's system-cancel (`exit` carrying its id — Android's gesture
monitor stealing the touch) cancels only that finger's press, without a
click; the other finger's gesture keeps running. -/
private def multiTouchCancel : IO Unit := do
  let aClicks ← IO.mkRef (0 : Nat)
  let bClicks ← IO.mkRef (0 : Nat)
  let srcs ← IO.mkRef (#[] : Array InteractionSource)
  let r ← rig <| Row do
    let srcA ← rememberInteractionSource
    let srcB ← rememberInteractionSource
    SideEffect (srcs.set #[srcA, srcB])
    leaf (Modifier.size 40 40 |>.clickable (aClicks.modify (· + 1)) (source := some srcA))
    leaf (Modifier.size 40 40 |>.clickable (bClicks.modify (· + 1)) (source := some srcB))
  let #[srcA, srcB] ← srcs.get | throw (IO.userError "interaction sources not captured")
  let _ ← r.im.pointerEvent (fingerPress 1 10 10)
  let _ ← r.im.pointerEvent (fingerPress 2 50 10)
  let _ ← r.im.pointerEvent (fingerCancel 1 10 10)
  check "finger cancel: A press cancelled" (!(← srcA.pressed.get))
  check "finger cancel: B still held" (← srcB.pressed.get)
  let _ ← r.im.pointerEvent (fingerRelease 2 50 10)
  checkEq "finger cancel: A never clicked" (← aClicks.get) 0
  checkEq "finger cancel: B clicked" (← bClicks.get) 1

/-- The mouse (pointer 0) and a finger are independent: a finger press on B
while the mouse holds A neither joins the mouse's capture nor disturbs its
click. -/
private def mouseAndFingerCoexist : IO Unit := do
  let aClicks ← IO.mkRef (0 : Nat)
  let bClicks ← IO.mkRef (0 : Nat)
  let r ← rig <| Row do
    leaf (Modifier.size 40 40 |>.clickable (aClicks.modify (· + 1)))
    leaf (Modifier.size 40 40 |>.clickable (bClicks.modify (· + 1)))
  let _ ← r.im.pointerEvent (pressAt 10 10)          -- mouse on A
  let _ ← r.im.pointerEvent (fingerPress 1 50 10)    -- finger on B
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  let _ ← r.im.pointerEvent (fingerRelease 1 50 10)
  checkEq "mouse+finger: mouse clicked A" (← aClicks.get) 1
  checkEq "mouse+finger: finger clicked B" (← bClicks.get) 1

/-! ## pointerInput lifecycle -/

/-- The handler coroutine relaunches when the key changes (predecessor
cancelled first) and is cancelled when the node leaves the composition. -/
private def pointerInputLifecycle : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let key ← MutableState.create (0 : UInt64)
  let show' ← MutableState.create true
  let r ← rig <| Tests.restartable 1 do
    if ← show'.get then
      withGroup 11 <| Box do
        let k ← liftM (m := IO) key.get
        leaf (Modifier.size 40 40 |>.pointerInput k
          (logEvents log s!"h{k}" (only := [.press, .release])))
    else
      withGroup 12 (pure ())
  let node ← (← r.root.child 0).child 0
  let some st0 := (← node.data).pointerInputs[0]?
    | throw (IO.userError "pointer state missing")
  let some j0 ← st0.job.get | throw (IO.userError "job missing")
  let _ ← r.im.pointerEvent (pressAt 5 5)
  let _ ← r.im.pointerEvent (releaseAt 5 5)
  checkEq "lifecycle: initial handler receives" (← log.get) #["h0:press", "h0:release"]
  -- Key change relaunches: the old coroutine is cancelled.
  key.set 1
  r.settle
  check "lifecycle: predecessor cancelled on key change" (← j0.isCancelled)
  log.set #[]
  let _ ← r.im.pointerEvent (pressAt 5 5)
  checkEq "lifecycle: only the new handler receives" (← log.get) #["h1:press"]
  let _ ← r.im.pointerEvent (releaseAt 5 5)
  -- Leaving the composition cancels.
  let some st1 := (← node.data).pointerInputs[0]?
    | throw (IO.userError "pointer state missing after relaunch")
  let some j1 ← st1.job.get | throw (IO.userError "job missing after relaunch")
  show'.set false
  r.settle
  check "lifecycle: cancelled on leave-composition" (← j1.isCancelled)

/-- Composing a `pointerInput` without an ambient scheduler throws (clear
misuse signal, like `LaunchedEffect`). -/
private def missingScheduler : IO Unit := do
  let root ← LayoutNode.create
  checkThrows "lifecycle: pointerInput without a LocalScheduler throws"
    (Composition.create (LayoutNode.applier root)
      (leaf (Modifier.size 10 10 |>.pointerInput 0 fun _ => pure ())))

/-! ## UiTask.race -/

/-- `race` completes with the first result and cancels the loser. -/
private def raceSemantics : IO Unit := do
  let (s, clock) ← fakeSched
  let log ← IO.mkRef (#[] : Array String)
  let _ ← s.launch do
    let v ← UiTask.race
      (do UiTask.delay 10; liftM (m := IO) (log.modify (·.push "fast")); pure "fast")
      (do UiTask.delay 30; liftM (m := IO) (log.modify (·.push "slow")); pure "slow")
    log.modify (·.push s!"won:{v}")
  s.runDue 0
  advance s clock (ms 50)
  checkEq "race: first result wins, loser cancelled" (← log.get) #["fast", "won:fast"]

/-! ## SDL translation (bootstrapped headless window) -/

/-- Software-renderer test config (the App-group pattern). -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

/-- End-to-end through `dispatchEvent` → `inputSink`: constructed `Sdl.Event`s
click, scroll (both wheel directions), traverse focus, deliver text, and
window-leave exits hover — with the recorder cursor and the M11 text-client
hook observed. -/
private def sdlTranslation : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let scrolls ← IO.mkRef (#[] : Array Offset)
  let texts ← IO.mkRef (#[] : Array String)
  let hook ← IO.mkRef (#[] : Array Bool)
  let ctx ← bootstrap "compose-input-test" 200 150
    (Box do
      leaf (Modifier.size 50 50
        |>.clickable (clicks.modify (· + 1))
        |>.onScroll (fun d => do scrolls.modify (·.push d); pure d)
        |>.onTextInput (fun t => do texts.modify (·.push t); pure true)))
    cfg
  let cursors ← IO.mkRef (#[] : Array Sdl.SystemCursor)
  let im ← installInput ctx (cursor := some { set := fun c => cursors.modify (·.push c) })
    (onTextClientFocused := fun b => hook.modify (·.push b))
  let _ ← step ctx cfg   -- starts the pointer coroutines and measures the tree
  let send (e : Sdl.Event) : IO Unit := dispatchEvent ctx cfg e
  -- Click through SDL button events.
  send (.mouseButtonDown ⟨0, ⟨0⟩, ⟨0⟩, .left, true, 1, 10, 10⟩)
  send (.mouseButtonUp ⟨0, ⟨0⟩, ⟨0⟩, .left, false, 1, 10, 10⟩)
  checkEq "sdl: button events click" (← clicks.get) 1
  -- Wheel at the mouse position; deltas pass through as delivered — the OS
  -- already applied the user's direction preference, so `.flipped` must NOT
  -- be negated (doing so reversed macOS natural trackpad scrolling).
  send (.mouseWheel ⟨0, ⟨0⟩, ⟨0⟩, 0, 2, .normal, 10, 10, 0, 2⟩)
  send (.mouseWheel ⟨0, ⟨0⟩, ⟨0⟩, 0, 2, .flipped, 10, 10, 0, 2⟩)
  checkEq "sdl: wheel deltas (flipped passes through)" (← scrolls.get)
    #[(⟨0, 2⟩ : Offset), (⟨0, 2⟩ : Offset)]
  -- Motion drives hover + cursor.
  send (.mouseMotion ⟨0, ⟨0⟩, ⟨0⟩, .none, 10, 10, 0, 0⟩)
  checkEq "sdl: hover sets the hand cursor" ((← cursors.get).map (·.val))
    #[Sdl.SystemCursor.pointer.val]
  -- Tab focuses the clickable (also a text client → hook fires true).
  send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .tab, .tab, .none, 0, true, false⟩)
  checkEq "sdl: tab focused a text client (M11 hook)" (← hook.get) #[true]
  -- Enter activates through the key path.
  send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .return, .return, .none, 0, true, false⟩)
  checkEq "sdl: Enter clicked the focused node" (← clicks.get) 2
  -- Text input reaches the focused node.
  send (.textInput ⟨0, ⟨0⟩, "hé"⟩)
  checkEq "sdl: text input routed" (← texts.get) #["hé"]
  -- Esc clears focus → the hook reports leaving the text client.
  send (.keyDown ⟨0, ⟨0⟩, ⟨0⟩, .escape, .escape, .none, 0, true, false⟩)
  checkEq "sdl: esc cleared the text client (M11 hook)" (← hook.get) #[true, false]
  -- Window leave exits hover and restores the cursor.
  send (.windowMouseLeave ⟨0, ⟨0⟩, 0, 0⟩)
  checkEq "sdl: window leave restores the cursor" ((← cursors.get).map (·.val))
    #[Sdl.SystemCursor.pointer.val, Sdl.SystemCursor.default.val]
  -- A touch tap through SDL finger events: normalized coordinates scale by
  -- the window size (200×150 here), and down+up land as one click.
  send (.fingerDown ⟨0, ⟨1⟩, ⟨0⟩, 0.05, 10.0 / 150.0, 0, 0, 1, ⟨0⟩⟩)
  send (.fingerUp ⟨0, ⟨1⟩, ⟨0⟩, 0.05, 10.0 / 150.0, 0, 0, 1, ⟨0⟩⟩)
  checkEq "sdl: finger tap clicks" (← clicks.get) 3
  -- A cancelled finger (gesture stolen by the system) does not click.
  send (.fingerDown ⟨0, ⟨1⟩, ⟨0⟩, 0.05, 10.0 / 150.0, 0, 0, 1, ⟨0⟩⟩)
  send (.fingerCanceled ⟨0, ⟨1⟩, ⟨0⟩, 0.05, 10.0 / 150.0, 0, 0, 1, ⟨0⟩⟩)
  checkEq "sdl: cancelled finger does not click" (← clicks.get) 3
  let _ ← im.pointerEvent (moveTo 0 0)   -- keep `im` alive for the whole test
  (← ctx.composition).dispose

/-! ## Input state across tree changes -/

/-- Removing the focused node by a state write (no click, no Esc) clears
focus through the normal path: `onFocusChanged false` fires, the M11
text-client hook reports `false` (the IME session ends), and later key/text
events reach nothing instead of the dead node. -/
private def focusDetachClears : IO Unit := do
  let hook ← IO.mkRef (#[] : Array Bool)
  let focusLog ← IO.mkRef (#[] : Array Bool)
  let keys ← IO.mkRef (0 : Nat)
  let show' ← MutableState.create true
  let ctx ← bootstrap "compose-focus-detach" 200 150
    (Tests.restartable 1 do
      if ← show'.get then
        withGroup 11 <| Box do
          leaf (Modifier.size 40 40 |>.focusable
            |>.onFocusChanged (fun b => focusLog.modify (·.push b))
            |>.onKeyEvent (fun _ => do keys.modify (· + 1); pure false)
            |>.onTextInput (fun _ => pure true))
      else
        withGroup 12 (pure ()))
    cfg
  let im ← installInput ctx (onTextClientFocused := fun b => hook.modify (·.push b))
  let _ ← step ctx cfg
  let _ ← im.keyEvent { key := .tab }   -- keyboard focus, no click involved
  checkEq "focus-detach: tab focused a text client" (← hook.get) #[true]
  checkEq "focus-detach: focus gained" (← focusLog.get) #[true]
  let _ ← im.keyEvent { key := .a }
  checkEq "focus-detach: keys route to the focused node" (← keys.get) 1
  -- Remove the focused node by a state write.
  show'.set false
  let _ ← step ctx cfg
  check "focus-detach: focus cleared on removal" ((← im.focus.focused).isNone)
  checkEq "focus-detach: onFocusChanged fired false" (← focusLog.get) #[true, false]
  checkEq "focus-detach: text-client hook fired false (IME stops)"
    (← hook.get) #[true, false]
  -- Later events go nowhere — not to the dead node's handlers.
  check "focus-detach: key events unhandled after removal"
    (!(← im.keyEvent { key := .a }))
  checkEq "focus-detach: dead handler never ran" (← keys.get) 1
  check "focus-detach: text input unhandled after removal" (!(← im.textInput "x"))
  (← ctx.composition).dispose

/-- The cursor icon set by a removed node is restored without mouse motion:
the post-layout hover sync recomputes the path and the icon. -/
private def hoverCursorResync : IO Unit := do
  let show' ← MutableState.create true
  let r ← rig <| Tests.restartable 1 do
    if ← show'.get then
      withGroup 11 <| leaf (Modifier.size 50 50 |>.pointerHoverIcon .text)
    else
      withGroup 12 (pure ())
  let _ ← r.im.pointerEvent (moveTo 10 10)
  checkEq "cursor-resync: icon set while hovered" ((← r.cursors.get).map (·.val))
    #[Sdl.SystemCursor.text.val]
  show'.set false
  r.settle
  checkEq "cursor-resync: default restored without mouse motion"
    ((← r.cursors.get).map (·.val)) (#[.text, .default].map Sdl.SystemCursor.val)

/-- MT scenario: a hoverable appearing under the stationary cursor (state
write, no mouse move) receives its `enter` — the post-layout hover sync
re-runs the path diff at the last known position. -/
private def hoverAppearUnderCursor : IO Unit := do
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let show' ← MutableState.create false
  Compose.Test.runComposeTest
    (Tests.restartable 1 do
      let src ← rememberInteractionSource
      SideEffect (srcCell.set (some src))
      if ← show'.get then
        withGroup 11 <| Box (modifier := Modifier.size 80 80 |>.hoverable src)
      else
        withGroup 12 (pure ())) do
      Compose.Test.mouseMove ⟨40, 40⟩
      Compose.Test.awaitIdle
      let some src ← srcCell.get | throw (IO.userError "source not captured")
      check "hover-sync: nothing hovered before it appears" (!(← src.hovered.get))
      show'.set true
      Compose.Test.awaitIdle
      check "hover-sync: appearing under the stationary cursor enters"
        (← src.hovered.get)

/-- MT scenario: a node removed while hovered gets its `exit` at detach time
(before its coroutines are cancelled), so a surviving remembered
`InteractionSource` does not stay latched hovered. -/
private def hoverDetachUnlatch : IO Unit := do
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let show' ← MutableState.create true
  Compose.Test.runComposeTest
    (Tests.restartable 1 do
      let src ← rememberInteractionSource
      SideEffect (srcCell.set (some src))
      if ← show'.get then
        withGroup 11 <| Box (modifier := Modifier.size 80 80 |>.hoverable src)
      else
        withGroup 12 (pure ())) do
      Compose.Test.mouseMove ⟨40, 40⟩
      Compose.Test.awaitIdle
      let some src ← srcCell.get | throw (IO.userError "source not captured")
      check "hover-unlatch: hovered while over" (← src.hovered.get)
      show'.set false
      Compose.Test.awaitIdle
      check "hover-unlatch: removal without a pointer exit un-latches"
        (!(← src.hovered.get))

/-! ## Drag scroll -/

private def pressT (x y : Float32) (t : UInt64) : PointerEvent :=
  { eventType := .press, position := ⟨x, y⟩, button := some .left, clicks := 1, timestamp := t }

private def moveT (x y : Float32) (t : UInt64) : PointerEvent :=
  { eventType := .move, position := ⟨x, y⟩, timestamp := t }

private def releaseT (x y : Float32) (t : UInt64) : PointerEvent :=
  { eventType := .release, position := ⟨x, y⟩, button := some .left, clicks := 1, timestamp := t }

/-- Drag-to-scroll steals the gesture from a pressed clickable past the
8dp axis slop: the pending click cancels (pressed interaction unlatched),
the content scrolls slop-adjusted then 1:1 — while a sub-slop wiggle and a
cross-axis drag stay clicks that move nothing. -/
private def dragScrollSteals : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      let src ← rememberInteractionSource
      SideEffect (srcCell.set (some src))
      leaf (Modifier.size 100 300 |>.clickable (clicks.modify (· + 1)) (source := some src))
  checkEq "drag-scroll: content overflows the viewport" (← st.maxValue) 200
  -- Press on the clickable, drag up past the slop: steal.
  let _ ← r.im.pointerEvent (pressAt 50 80)
  let some src ← srcCell.get | throw (IO.userError "source not captured")
  check "drag-scroll: pressed on the child" (← src.pressed.get)
  let _ ← r.im.pointerEvent (moveTo 50 40)
  checkEq "drag-scroll: past the slop the content scrolls (slop-adjusted)"
    (← st.value) 32
  check "drag-scroll: the stolen press unlatched" (!(← src.pressed.get))
  let _ ← r.im.pointerEvent (moveTo 50 20)
  checkEq "drag-scroll: further moves scroll 1:1" (← st.value) 52
  let _ ← r.im.pointerEvent (releaseAt 50 20)
  checkEq "drag-scroll: the stolen click never fires" (← clicks.get) 0
  -- Sub-slop wiggle: still a click, nothing scrolls.
  let _ ← r.im.pointerEvent (pressAt 50 80)
  let _ ← r.im.pointerEvent (moveTo 50 76)
  let _ ← r.im.pointerEvent (releaseAt 50 76)
  checkEq "drag-scroll: a sub-slop press stays a click" (← clicks.get) 1
  checkEq "drag-scroll: a sub-slop press moves nothing" (← st.value) 52
  -- Cross-axis drag: not this container's gesture; the click survives.
  let _ ← r.im.pointerEvent (pressAt 50 80)
  let _ ← r.im.pointerEvent (moveTo 80 80)
  let _ ← r.im.pointerEvent (releaseAt 80 80)
  checkEq "drag-scroll: a cross-axis drag leaves the click alone" (← clicks.get) 2
  checkEq "drag-scroll: a cross-axis drag moves nothing" (← st.value) 52

/-- Releasing a drag with tracked velocity flings: the offset keeps advancing
on frame ticks after the release, and a fresh press catches (freezes) it. -/
private def dragScrollFlingAndCatch : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 5000)
  -- Uniform 1250 px/s upward drag.
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  checkEq "fling: dragged before release" (← st.value) 52
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)      -- starts the fling coroutine
  r.s.tickFrame (ms 60)            -- fling's t₀
  r.s.tickFrame (ms 76)            -- first decay step
  let v1 ← st.value
  check s!"fling: coasts after release ({v1})" (v1 > 52)
  r.s.tickFrame (ms 92)
  let v2 ← st.value
  check s!"fling: keeps decaying forward ({v1} → {v2})" (v2 > v1)
  -- The catch: touching down stops the fling where it is.
  let _ ← r.im.pointerEvent (pressT 50 50 (ms 100))
  r.s.tickFrame (ms 108)
  r.s.tickFrame (ms 124)
  checkEq "fling: a press catches it" (← st.value) v2
  let _ ← r.im.pointerEvent (releaseT 50 50 (ms 130))

/-- A fling that reaches the end of the range stops there (no oscillation,
no overshoot past `maxValue`). -/
private def dragScrollFlingEndStop : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)
  for i in [0:24] do
    r.s.tickFrame (ms (60 + 16 * i.toUInt64))
  checkEq "fling: stops pinned at the end of the range" (← st.value) 200

/-- An inner drag gesture (a slider) that consumes its moves owns the
gesture: the scroll container stands off for its remainder. -/
private def dragScrollInnerDragWins : IO Unit := do
  let drags ← IO.mkRef (0 : Nat)
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300 |>.pointerInput 1
        (detectDragGestures (fun _ _ => drags.modify (· + 1))))
  let _ ← r.im.pointerEvent (pressAt 50 80)
  let _ ← r.im.pointerEvent (moveTo 50 70)  -- past the inner 4px slop first
  let _ ← r.im.pointerEvent (moveTo 50 40)
  let _ ← r.im.pointerEvent (releaseAt 50 40)
  check "inner drag: the inner detector dragged" ((← drags.get) ≥ 2)
  checkEq "inner drag: the scroll container stood off" (← st.value) 0

/-- A second finger landing mid-gesture must not corrupt a drag-scroll
session: the handler latches the arming pointer, so a foreign pointer's
presses/moves/releases pass through untouched and the session's drag math
stays anchored to its own origin. -/
private def dragScrollIgnoresSecondFinger : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (fingerPress 1 50 80)
  let _ ← r.im.pointerEvent (fingerPress 2 20 90)
  let _ ← r.im.pointerEvent (fingerMove 2 20 20)  -- far past the slop
  checkEq "second finger: a foreign move does not scroll the session"
    (← st.value) 0
  let _ ← r.im.pointerEvent (fingerMove 1 50 40)
  checkEq "second finger: the session pointer drags from its own origin"
    (← st.value) 32
  let _ ← r.im.pointerEvent (fingerRelease 2 20 20)
  let _ ← r.im.pointerEvent (fingerMove 1 50 20)
  checkEq "second finger: a foreign release does not end the session"
    (← st.value) 52
  let _ ← r.im.pointerEvent (fingerRelease 1 50 20)

/-! ## Nested scroll (drag + fling) -/

/-- Shared rig: a 100px vertical outer (content 400) holding a 100px vertical
inner (content 150, `maxValue` 50) above 300px of filler. -/
private def nestedRig (outer inner : ScrollState) : Composable Unit :=
  Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll outer) do
      Column do
        Box (modifier := Modifier.size 100 100 |>.verticalScroll inner) do
          leaf (Modifier.size 100 150)
        leaf (Modifier.size 100 300)

/-- An end-stopped inner hands unconsumed drag motion to the outer 1:1;
reversing direction feeds the inner first again while the outer holds. -/
private def nestedDragHandsOff : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| nestedRig outer inner
  checkEq "nested drag: inner range" (← inner.maxValue) 50
  checkEq "nested drag: outer range" (← outer.maxValue) 300
  let _ ← r.im.pointerEvent (pressAt 50 90)
  let _ ← r.im.pointerEvent (moveTo 50 60)   -- steal: inner takes 22
  checkEq "nested drag: inner consumes first" (← inner.value) 22
  checkEq "nested drag: outer holds while inner has range" (← outer.value) 0
  let _ ← r.im.pointerEvent (moveTo 50 32)   -- inner tops out exactly (50)
  checkEq "nested drag: inner pinned at its end" (← inner.value) 50
  checkEq "nested drag: nothing spilled yet" (← outer.value) 0
  let _ ← r.im.pointerEvent (moveTo 50 20)   -- fully end-stopped: outer follows
  checkEq "nested drag: inner stays pinned" (← inner.value) 50
  checkEq "nested drag: the remainder scrolls the outer 1:1" (← outer.value) 12
  -- Reversal: the inner leaves its end-stop first, the outer freezes.
  let _ ← r.im.pointerEvent (moveTo 50 40)
  checkEq "nested drag: reversing feeds the inner first" (← inner.value) 30
  checkEq "nested drag: the outer holds on reversal" (← outer.value) 12
  let _ ← r.im.pointerEvent (releaseAt 50 40)

/-- A release with the inner parked at its end-stop hands the tracked
velocity to the outer, which flings; the inner stays pinned. -/
private def nestedFlingHandoff : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| nestedRig outer inner
  -- Uniform 1250 px/s upward drag that parks the inner at 50 before release.
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  checkEq "nested fling: inner parked at the end" (← inner.value) 50
  let outerAtRelease ← outer.value
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)      -- starts the outer's fling coroutine
  r.s.tickFrame (ms 60)
  r.s.tickFrame (ms 76)
  let v1 ← outer.value
  check s!"nested fling: the outer coasts ({v1})" (v1 > outerAtRelease)
  r.s.tickFrame (ms 92)
  check "nested fling: keeps decaying" ((← outer.value) > v1)
  checkEq "nested fling: the inner never moves past its end" (← inner.value) 50

/-- A release with the inner mid-range flings the inner itself; the outer
gets nothing. -/
private def nestedFlingNotAtStop : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| nestedRig outer inner
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 60 (ms 32))
  checkEq "nested fling mid: inner mid-range" (← inner.value) 22
  let _ ← r.im.pointerEvent (releaseT 50 60 (ms 40))
  advance r.s r.clock (ms 40)
  r.s.tickFrame (ms 44)
  r.s.tickFrame (ms 60)
  r.s.tickFrame (ms 76)
  check s!"nested fling mid: the inner flings ({← inner.value})"
    ((← inner.value) > 22)
  checkEq "nested fling mid: the outer stays put" (← outer.value) 0

/-- A horizontal outer over an end-stopped vertical inner: the vertical
leftover has no horizontal component, so the outer never moves. -/
private def nestedCrossAxis : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.horizontalScroll outer) do
      Row do
        Box (modifier := Modifier.size 100 100 |>.verticalScroll inner) do
          leaf (Modifier.size 100 120)
        leaf (Modifier.size 300 100)
  let _ ← r.im.pointerEvent (pressAt 50 90)
  let _ ← r.im.pointerEvent (moveTo 50 40)
  let _ ← r.im.pointerEvent (moveTo 50 20)
  checkEq "nested cross-axis: inner pinned at its end" (← inner.value) 20
  checkEq "nested cross-axis: the horizontal outer never moves" (← outer.value) 0
  let _ ← r.im.pointerEvent (releaseAt 50 20)

/-- Three nested verticals: the innermost tops out, the middle consumes the
remainder to its own end, the outer takes the rest — one event cascades
through all three. -/
private def threeLevelCascade : IO Unit := do
  let outer ← ScrollState.create
  let middle ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll outer) do
      Column do
        Box (modifier := Modifier.size 100 100 |>.verticalScroll middle) do
          Column do
            Box (modifier := Modifier.size 100 100 |>.verticalScroll inner) do
              leaf (Modifier.size 100 110)
            leaf (Modifier.size 100 20)
        leaf (Modifier.size 100 300)
  checkEq "cascade: inner range" (← inner.maxValue) 10
  checkEq "cascade: middle range" (← middle.maxValue) 20
  let _ ← r.im.pointerEvent (pressAt 50 90)
  let _ ← r.im.pointerEvent (moveTo 50 40)   -- 42px past the slop, one event
  checkEq "cascade: inner filled" (← inner.value) 10
  checkEq "cascade: middle filled" (← middle.value) 20
  checkEq "cascade: outer takes the rest" (← outer.value) 12
  let _ ← r.im.pointerEvent (moveTo 50 30)   -- both stops hit: outer 1:1
  checkEq "cascade: further motion all outer" (← outer.value) 22
  let _ ← r.im.pointerEvent (releaseAt 50 30)

/-- `onDispatchEnd` runs after the whole leaf→root sweep with the surviving
leftover: the inner (gesture-owner analog) registers on each move, the outer
final-pass observer rewrites the published leftover afterwards — the
finalizer must see the outer's value, not the inner's. -/
private partial def finalizerInner (log : IO.Ref (Array String))
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .move then
    ev.setLeftover ⟨0, 30⟩
    ev.onDispatchEnd fun l? => do
      let s := match l? with
        | some l => s!"{l.x.toInt32},{l.y.toInt32}"
        | none => "none"
      log.modify (·.push s!"end:{s}")
  finalizerInner log scope

private partial def finalizerOuter (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  if ev.eventType == .move then
    if let some l ← ev.getLeftover then
      ev.setLeftover ⟨l.x, l.y - 20⟩
  finalizerOuter scope

private def dispatchEndFinalizer : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let r ← rig <| Box (modifier := Modifier.size 100 100
      |>.pointerInput 2 finalizerOuter (pass := .final)) do
    leaf (Modifier.size 50 50 |>.pointerInput 1 (finalizerInner log) (pass := .final))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (moveTo 12 12)
  checkEq "dispatch-end: the finalizer sees the post-sweep leftover"
    (← log.get) #["end:0,10"]
  let _ ← r.im.pointerEvent (releaseAt 12 12)

/-! ## Transform gestures -/

/-- Record of one `onTransform` step. -/
private structure TransformCall where
  centroid : Offset
  pan : Offset
  zoom : Float32
  rotation : Float32
  deriving Inhabited

private def approxF (a b : Float32) (eps : Float32 := 0.001) : Bool :=
  (a - b).abs ≤ eps

/-- Two diverging fingers cross the transform slop and stream zoom steps;
one finger alone never fires. -/
private def transformZoomFires : IO Unit := do
  let calls ← IO.mkRef (#[] : Array TransformCall)
  let stCell ← IO.mkRef (none : Option TransformableState)
  let r ← rig <| Box do
    let st ← rememberTransformableState fun c pan zoom rot =>
      calls.modify (·.push ⟨c, pan, zoom, rot⟩)
    SideEffect (stCell.set (some st))
    leaf (Modifier.size 100 100 |>.transformable st)
  -- One finger dragging is not a transform.
  let _ ← r.im.pointerEvent (fingerPress 1 40 50)
  let _ ← r.im.pointerEvent (fingerMove 1 10 50)
  let _ ← r.im.pointerEvent (fingerRelease 1 10 50)
  checkEq "transform: a single finger never fires" (← calls.get).size 0
  -- Two fingers diverge: under slop first, then the crossing step fires.
  let _ ← r.im.pointerEvent (fingerPress 1 40 50)
  let _ ← r.im.pointerEvent (fingerPress 2 60 50)
  let _ ← r.im.pointerEvent (fingerMove 1 30 50)   -- motion 7.5 < 8: pending
  checkEq "transform: under the slop nothing fires" (← calls.get).size 0
  let _ ← r.im.pointerEvent (fingerMove 2 70 50)   -- motion 20 > 8: fires
  let cs ← calls.get
  checkEq "transform: crossing the slop fires once" cs.size 1
  check s!"transform: the crossing step's zoom ({cs[0]!.zoom})"
    (approxF cs[0]!.zoom (4.0 / 3.0))
  checkEq "transform: centroid at the pointer mean" cs[0]!.centroid ⟨50, 50⟩
  checkEq "transform: pure spread has no rotation" cs[0]!.rotation 0
  let _ ← r.im.pointerEvent (fingerMove 1 20 50)   -- active: fires per move
  let cs ← calls.get
  checkEq "transform: active streams per move" cs.size 2
  check s!"transform: second step's zoom ({cs[1]!.zoom})"
    (approxF cs[1]!.zoom 1.25)
  let _ ← r.im.pointerEvent (fingerRelease 1 20 50)
  let _ ← r.im.pointerEvent (fingerRelease 2 70 50)

/-- A pinch on a transformable inside a scrollable zooms — the scroll stays
put and a pending click under a finger cancels; below two fingers the
scrollable still owns single-finger drags. -/
private def transformStealsFromScrollable : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let clicks ← IO.mkRef (0 : Nat)
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let scroll ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll scroll) do
      let st ← rememberTransformableState fun _ _ _ _ => calls.modify (· + 1)
      Box (modifier := Modifier.size 100 300 |>.transformable st) do
        let src ← rememberInteractionSource
        SideEffect (srcCell.set (some src))
        leaf (Modifier.size 100 300 |>.clickable (clicks.modify (· + 1))
          (source := some src))
  let some src ← srcCell.get | throw (IO.userError "source not captured")
  -- Symmetric vertical pinch: each finger stays under the scroll slop while
  -- the spread crosses the transform slop.
  let _ ← r.im.pointerEvent (fingerPress 1 50 40)
  check "transform-steal: pressed on the child" (← src.pressed.get)
  let _ ← r.im.pointerEvent (fingerPress 2 50 60)
  let _ ← r.im.pointerEvent (fingerMove 1 50 34)   -- transform 3.9, scroll 6: neither
  checkEq "transform-steal: under both slops nothing moves" (← scroll.value) 0
  let _ ← r.im.pointerEvent (fingerMove 2 50 66)   -- transform 9.6 > 8: steal
  check "transform-steal: the pinch crossed first" ((← calls.get) ≥ 1)
  check "transform-steal: the pending press unlatched" (!(← src.pressed.get))
  let _ ← r.im.pointerEvent (fingerMove 1 50 30)   -- active: consumed move
  checkEq "transform-steal: the scrollable never moved" (← scroll.value) 0
  let _ ← r.im.pointerEvent (fingerRelease 1 50 30)
  let _ ← r.im.pointerEvent (fingerRelease 2 50 66)
  checkEq "transform-steal: the stolen click never fires" (← clicks.get) 0
  -- A single finger on the same tree still drag-scrolls.
  let before ← calls.get
  let _ ← r.im.pointerEvent (fingerPress 1 50 80)
  let _ ← r.im.pointerEvent (fingerMove 1 50 40)
  let _ ← r.im.pointerEvent (fingerRelease 1 50 40)
  checkEq "transform-steal: one finger scrolls the parent" (← scroll.value) 32
  checkEq "transform-steal: one finger never transforms" (← calls.get) before

/-- A finger cancel (system-stolen gesture) mid-transform drops the gesture;
a fresh second press starts over with fresh slop accumulation. -/
private def transformCancelDrops : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let r ← rig <| Box do
    let st ← rememberTransformableState fun _ _ _ _ => calls.modify (· + 1)
    leaf (Modifier.size 100 100 |>.transformable st)
  let _ ← r.im.pointerEvent (fingerPress 1 40 50)
  let _ ← r.im.pointerEvent (fingerPress 2 60 50)
  let _ ← r.im.pointerEvent (fingerMove 1 30 50)
  let _ ← r.im.pointerEvent (fingerMove 2 70 50)
  checkEq "transform-cancel: active" (← calls.get) 1
  let _ ← r.im.pointerEvent (fingerCancel 1 30 50)
  let _ ← r.im.pointerEvent (fingerMove 2 60 50)
  checkEq "transform-cancel: below two fingers nothing fires" (← calls.get) 1
  -- Re-press: accumulators start fresh — a small step stays under the slop.
  let _ ← r.im.pointerEvent (fingerPress 1 40 50)
  let _ ← r.im.pointerEvent (fingerMove 2 62 50)
  checkEq "transform-cancel: a new gesture accumulates from zero" (← calls.get) 1
  let _ ← r.im.pointerEvent (fingerRelease 1 40 50)
  let _ ← r.im.pointerEvent (fingerRelease 2 62 50)

/-- SDL trackpad pinch events route to the transformable under the cursor —
scale-only, no slop — but never while a finger gesture is live (Android
sends both streams for one pinch; consuming both would double-apply). -/
private def transformPinchEventRouting : IO Unit := do
  let calls ← IO.mkRef (#[] : Array TransformCall)
  let r ← rig <| Box do
    let st ← rememberTransformableState fun c pan zoom rot =>
      calls.modify (·.push ⟨c, pan, zoom, rot⟩)
    leaf (Modifier.size 100 100 |>.transformable st)
  let conv (x y : Float32) : IO Offset := pure ⟨x, y⟩
  -- Cursor over the element: a pinch step fires directly.
  let _ ← r.im.pointerEvent (moveTo 50 50)
  let _ ← r.im.sdlEvent conv (.pinchUpdate ⟨0, 1.5, ⟨0⟩⟩)
  let cs ← calls.get
  checkEq "pinch event: routed at the cursor" cs.size 1
  check s!"pinch event: scale carries ({cs[0]!.zoom})" (approxF cs[0]!.zoom 1.5)
  checkEq "pinch event: at the last mouse position" cs[0]!.centroid ⟨50, 50⟩
  -- Begin/end are swallowed without effect.
  let _ ← r.im.sdlEvent conv (.pinchBegin ⟨0, 1, ⟨0⟩⟩)
  let _ ← r.im.sdlEvent conv (.pinchEnd ⟨0, 1, ⟨0⟩⟩)
  checkEq "pinch event: begin/end carry nothing" (← calls.get).size 1
  -- A live finger gesture gates the duplicate stream off.
  let _ ← r.im.pointerEvent (fingerPress 1 30 50)
  let _ ← r.im.sdlEvent conv (.pinchUpdate ⟨0, 2.0, ⟨0⟩⟩)
  checkEq "pinch event: gated while a finger is captured" (← calls.get).size 1
  let _ ← r.im.pointerEvent (fingerRelease 1 30 50)
  let _ ← r.im.sdlEvent conv (.pinchUpdate ⟨0, 1.25, ⟨0⟩⟩)
  checkEq "pinch event: flows again after the finger lifts" (← calls.get).size 2

/-! ## Overscroll bounce -/

/-- Dragging past the start rubber-bands (sub-linear, value pinned), keeps
stretching in raw space, and a reversal unwinds the band before the content
scrolls again; a resting release springs the band monotonically back. -/
private def dragRubberBand : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st (overscroll := .bounce)) do
      leaf (Modifier.size 100 300)
  -- Pull down at the top: 32 post-slop px band to rubberBand 32 ≈ 14.97.
  let _ ← r.im.pointerEvent (pressAt 50 20)
  let _ ← r.im.pointerEvent (moveTo 50 60)
  checkEq "rubber band: value pinned at the start" (← st.value) 0
  let o1 ← st.overscroll
  check s!"rubber band: the band grows sub-linearly ({o1})"
    (approxF o1 14.966 0.01)
  -- Further pull stretches in raw space: rubberBand (32+20) ≈ 22.24.
  let _ ← r.im.pointerEvent (moveTo 50 80)
  let o2 ← st.overscroll
  check s!"rubber band: keeps stretching ({o2})" (approxF o2 22.239 0.01)
  -- Reversal: 52 raw px unwind first, the 8 px remainder scrolls.
  let _ ← r.im.pointerEvent (moveTo 50 20)
  checkEq "rubber band: reversal unwinds before scrolling" (← st.overscroll) 0
  check s!"rubber band: the crossing remainder scrolls ({← st.value})"
    (approxF (← st.value) 8 0.001)
  let _ ← r.im.pointerEvent (releaseAt 50 20)
  -- A fresh stretch (the value scrolls its 8 px back to the start first,
  -- the 44 unconsumed px band) released at rest springs back monotonically.
  let _ ← r.im.pointerEvent (pressT 50 30 0)
  let _ ← r.im.pointerEvent (moveT 50 90 (ms 16))
  check "rubber band: stretched again" ((← st.overscroll) > 19)
  let _ ← r.im.pointerEvent (releaseT 50 90 (ms 66))   -- rest gap: v = 0
  advance r.s r.clock (ms 66)
  r.s.tickFrame (ms 70)
  let mut prev ← st.overscroll
  for i in [0:32] do
    r.s.tickFrame (ms (86 + 16 * i.toUInt64))
    let o ← st.overscroll
    check s!"rubber band: spring-back is monotone ({prev} → {o})" (o ≤ prev)
    prev := o
  checkEq "rubber band: settles at rest" (← st.overscroll) 0
  checkEq "rubber band: the spring leaves the value alone" (← st.value) 0

/-- A fling that reaches the end of the range overshoots into overscroll
(the residual momentum), then settles back to exactly the end. -/
private def bounceOvershootThenSettle : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st (overscroll := .bounce)) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)
  let mut oMin : Float32 := 0
  for i in [0:60] do
    r.s.tickFrame (ms (60 + 16 * i.toUInt64))
    oMin := min oMin (← st.overscroll)
    check "bounce: the value never leaves the range" ((← st.value) ≤ 200)
  check s!"bounce: overshoots past the end ({oMin})" (oMin < -1)
  checkEq "bounce: settles back to the end" (← st.overscroll) 0
  checkEq "bounce: pinned at the end of the range" (← st.value) 200

/-- `overscroll := .none` keeps the hard stop: drags pin without a band and
an end-stopped fling never overshoots. -/
private def overscrollOptOut : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st (overscroll := .none)) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressAt 50 20)
  let _ ← r.im.pointerEvent (moveTo 50 80)
  checkEq "bounce off: a drag past the start pins without a band" (← st.value) 0
  checkEq "bounce off: no overscroll from drags" (← st.overscroll) 0
  let _ ← r.im.pointerEvent (releaseAt 50 80)
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)
  for i in [0:40] do
    r.s.tickFrame (ms (60 + 16 * i.toUInt64))
    checkEq "bounce off: a fling never overshoots" (← st.overscroll) 0
  checkEq "bounce off: hard stop at the end" (← st.value) 200

/-- A press mid-bounce catches (freezes) the spring like it catches a
fling; releasing without a drag lets the caught band settle. -/
private def catchDuringBounce : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st (overscroll := .bounce)) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 30 0)
  let _ ← r.im.pointerEvent (moveT 50 90 (ms 16))
  let _ ← r.im.pointerEvent (releaseT 50 90 (ms 66))   -- rest gap: pure spring
  advance r.s r.clock (ms 66)
  r.s.tickFrame (ms 70)
  r.s.tickFrame (ms 86)
  let mid ← st.overscroll
  check s!"catch bounce: mid-spring ({mid})" (mid > 0 && mid < 22.2)
  let _ ← r.im.pointerEvent (pressT 50 50 (ms 90))
  r.s.tickFrame (ms 102)
  r.s.tickFrame (ms 118)
  checkEq "catch bounce: the press freezes the band" (← st.overscroll) mid
  let _ ← r.im.pointerEvent (releaseT 50 50 (ms 120))
  advance r.s r.clock (ms 120)
  for i in [0:40] do
    r.s.tickFrame (ms (124 + 16 * i.toUInt64))
  checkEq "catch bounce: a click lets the caught band settle" (← st.overscroll) 0

/-- With inner and outer both end-stopped, the band lands on the gesture
owner (the inner), never the following outer — Android's innermost edge
effect. -/
private def nestedBounceLandsOnOwner : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll outer (overscroll := .bounce)) do
      Column do
        Box (modifier := Modifier.size 100 100 |>.verticalScroll inner (overscroll := .bounce)) do
          leaf (Modifier.size 100 150)
        leaf (Modifier.size 100 30)
  checkEq "nested bounce: inner range" (← inner.maxValue) 50
  checkEq "nested bounce: outer range" (← outer.maxValue) 30
  let _ ← r.im.pointerEvent (pressAt 50 95)
  let _ ← r.im.pointerEvent (moveTo 50 30)   -- inner fills (50), outer takes 7
  let _ ← r.im.pointerEvent (moveTo 50 5)    -- outer fills (30), 2 px survive
  checkEq "nested bounce: inner pinned" (← inner.value) 50
  checkEq "nested bounce: outer pinned" (← outer.value) 30
  let oi ← inner.overscroll
  check s!"nested bounce: the owner bands the survivors ({oi})"
    (approxF oi (-1.088) 0.01)
  checkEq "nested bounce: the following outer never bands" (← outer.overscroll) 0
  let _ ← r.im.pointerEvent (releaseAt 50 5)
  advance r.s r.clock (ms 1)
  for i in [0:40] do
    r.s.tickFrame (ms (16 + 16 * i.toUInt64))
  checkEq "nested bounce: the owner's band settles" (← inner.overscroll) 0

/-- Wheel scrolling never rubber-bands (the AOSP mouse-source rule), and a
wheel event snaps a standing band. -/
private def wheelNoBounce : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  for _ in [0:5] do
    let _ ← r.im.pointerEvent (scrollAt 50 50 ⟨0, -1⟩)
  checkEq "wheel: reaches the end" (← st.value) 200
  let _ ← r.im.pointerEvent (scrollAt 50 50 ⟨0, -1⟩)
  checkEq "wheel: pinned at the end" (← st.value) 200
  checkEq "wheel: never bands" (← st.overscroll) 0
  -- Drag past the end to raise a band, then wheel: the band snaps.
  let _ ← r.im.pointerEvent (pressAt 50 80)
  let _ ← r.im.pointerEvent (moveTo 50 10)
  check "wheel: the drag banded past the end" ((← st.overscroll) < 0)
  let _ ← r.im.pointerEvent (releaseAt 50 10)
  let _ ← r.im.pointerEvent (scrollAt 50 50 ⟨0, 1⟩)
  checkEq "wheel: snaps a standing band" (← st.overscroll) 0
  checkEq "wheel: and scrolls normally" (← st.value) 150

/-! ## Overscroll stretch (the default mode) -/

/-- Dragging past the start in stretch mode accumulates the *raw* pull 1:1
(the damping is visual, applied at draw time by `stretchIntensity`), pins
the value, and a reversal unwinds the band before the content scrolls. -/
private def stretchDragAccumulates : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressAt 50 20)
  let _ ← r.im.pointerEvent (moveTo 50 60)   -- 40 px pull, 32 post-slop
  checkEq "stretch drag: value pinned at the start" (← st.value) 0
  checkEq "stretch drag: the raw pull accumulates 1:1" (← st.overscroll) 32
  let _ ← r.im.pointerEvent (moveTo 50 80)
  checkEq "stretch drag: keeps accumulating" (← st.overscroll) 52
  let _ ← r.im.pointerEvent (moveTo 50 20)
  checkEq "stretch drag: reversal unwinds before scrolling" (← st.overscroll) 0
  check s!"stretch drag: the crossing remainder scrolls ({← st.value})"
    (approxF (← st.value) 8 0.001)
  let _ ← r.im.pointerEvent (releaseAt 50 20)

/-- A release from rest runs the EdgeEffect spring home: the band never
grows, settles at exactly 0, and the value is untouched. -/
private def stretchReleaseSpringsBack : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 30 0)
  let _ ← r.im.pointerEvent (moveT 50 90 (ms 16))   -- 52 post-slop band
  checkEq "stretch spring: banded raw" (← st.overscroll) 52
  let _ ← r.im.pointerEvent (releaseT 50 90 (ms 66))   -- rest gap: v = 0
  advance r.s r.clock (ms 66)
  r.s.tickFrame (ms 70)
  let mut prev ← st.overscroll
  for i in [0:40] do
    r.s.tickFrame (ms (86 + 16 * i.toUInt64))
    let o ← st.overscroll
    check s!"stretch spring: never grows on a rest release ({prev} → {o})"
      (o ≤ prev + 0.01)
    prev := o
  checkEq "stretch spring: settles at rest" (← st.overscroll) 0
  checkEq "stretch spring: the value is untouched" (← st.value) 0

/-- A fling that reaches the end absorbs its residual velocity ×13
(`EdgeEffect.onAbsorb`) into the band, then settles back to exactly the
end — the value never leaves the range. -/
private def stretchFlingAbsorb : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 90 0)
  let _ ← r.im.pointerEvent (moveT 50 70 (ms 16))
  let _ ← r.im.pointerEvent (moveT 50 50 (ms 32))
  let _ ← r.im.pointerEvent (moveT 50 30 (ms 48))
  let _ ← r.im.pointerEvent (releaseT 50 30 (ms 56))
  advance r.s r.clock (ms 56)
  let mut oMin : Float32 := 0
  for i in [0:80] do
    r.s.tickFrame (ms (60 + 16 * i.toUInt64))
    oMin := min oMin (← st.overscroll)
    check "stretch absorb: the value never leaves the range" ((← st.value) ≤ 200)
  check s!"stretch absorb: the ×13 absorb dips well past the end ({oMin})" (oMin < -4)
  checkEq "stretch absorb: settles back" (← st.overscroll) 0
  checkEq "stretch absorb: pinned at the end" (← st.value) 200

/-- A press mid-settle catches (freezes) the band like it catches a fling;
releasing without a drag lets the caught band settle. -/
private def stretchCatchFreezes : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let _ ← r.im.pointerEvent (pressT 50 30 0)
  let _ ← r.im.pointerEvent (moveT 50 90 (ms 16))
  let _ ← r.im.pointerEvent (releaseT 50 90 (ms 66))
  advance r.s r.clock (ms 66)
  r.s.tickFrame (ms 70)
  r.s.tickFrame (ms 86)
  let mid ← st.overscroll
  check s!"stretch catch: mid-settle ({mid})" (mid > 0 && mid < 52)
  let _ ← r.im.pointerEvent (pressT 50 50 (ms 90))
  r.s.tickFrame (ms 102)
  r.s.tickFrame (ms 118)
  checkEq "stretch catch: the press freezes the band" (← st.overscroll) mid
  let _ ← r.im.pointerEvent (releaseT 50 50 (ms 120))
  advance r.s r.clock (ms 120)
  for i in [0:40] do
    r.s.tickFrame (ms (124 + 16 * i.toUInt64))
  checkEq "stretch catch: a click lets the caught band settle" (← st.overscroll) 0

/-- With inner and outer both end-stopped, the band lands on the gesture
owner (the inner) with the *raw* surviving motion, never the following
outer — Android's innermost edge effect, stretch flavor. -/
private def nestedStretchLandsOnOwner : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll outer) do
      Column do
        Box (modifier := Modifier.size 100 100 |>.verticalScroll inner) do
          leaf (Modifier.size 100 150)
        leaf (Modifier.size 100 30)
  let _ ← r.im.pointerEvent (pressAt 50 95)
  let _ ← r.im.pointerEvent (moveTo 50 30)   -- inner fills (50), outer takes 7
  let _ ← r.im.pointerEvent (moveTo 50 5)    -- outer fills (30), 2 px survive
  checkEq "nested stretch: inner pinned" (← inner.value) 50
  checkEq "nested stretch: outer pinned" (← outer.value) 30
  checkEq "nested stretch: the owner bands the raw survivors" (← inner.overscroll) (-2)
  checkEq "nested stretch: the following outer never bands" (← outer.overscroll) 0
  let _ ← r.im.pointerEvent (releaseAt 50 5)
  advance r.s r.clock (ms 1)
  for i in [0:40] do
    r.s.tickFrame (ms (16 + 16 * i.toUInt64))
  checkEq "nested stretch: the owner's band settles" (← inner.overscroll) 0

/-- The frame a stretch-banded container draws contains exactly one warp
layer under the scroll clip, carrying the `stretchIntensity`-damped
intensity; at rest there is none. -/
private def stretchModeRecordsWarpLayer : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      leaf (Modifier.size 100 300)
  let hasStretch (list : Compose.Draw.DisplayList) : Bool :=
    list.any (fun p => (p.brief.splitOn "stretch=").length > 1)
  let (rest, _) ← Compose.Draw.DrawScope.record {} r.root.drawTree
  check "stretch layer: none at rest" (!hasStretch rest)
  let _ ← r.im.pointerEvent (pressAt 50 20)
  let _ ← r.im.pointerEvent (moveTo 50 60)   -- band 32 on a 100 px viewport
  let _ ← r.root.remeasure { maxWidth := 200, maxHeight := 200 }
  let (banded, _) ← Compose.Draw.DrawScope.record {} r.root.drawTree
  let tag := s!"stretch=(0,{Compose.Draw.fmtF (stretchIntensity 32 100)})"
  let briefs := String.intercalate "\n" (banded.map (·.brief)).toList
  check s!"stretch layer: one warp layer with the damped intensity ({tag})"
    ((briefs.splitOn tag).length == 2)
  check "stretch layer: recorded under the scroll clip"
    ((briefs.splitOn s!"clip=(0,0,100,100) bounds=").length == 2)
  let _ ← r.im.pointerEvent (releaseAt 50 60)

/-! ## Bring into view -/

/-- The reveal dispatcher: a below-the-fold focusable scrolls the minimal
amount into view (bottom to the edge), an above-the-fold one the other way
(top to the edge), an already-visible request neither moves nor interrupts,
and a wheel mid-reveal stands the animation down. -/
private def bringIntoViewReveal : IO Unit := do
  let st ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll st) do
      Column do
        leaf (Modifier.size 100 150)
        leaf (Modifier.size 100 20 |>.focusable)
        leaf (Modifier.size 100 130)
  check "reveal: tab focuses the target" (← r.im.keyEvent { key := .tab })
  let some n ← r.im.focus.focused | throw (IO.userError "reveal: nothing focused")
  n.bringIntoView r.s
  advance r.s r.clock (ms 1)
  for i in [0:26] do
    r.s.tickFrame (ms (16 + 16 * i.toUInt64))
  checkEq "reveal below: minimal scroll, bottom to the edge" (← st.value) 70
  -- Already visible: nothing moves, nothing is interrupted. (The real
  -- pipeline services requests post-measure — the rig remeasures by hand.)
  r.settle
  let gen ← st.mutationGen.get
  n.bringIntoView r.s
  advance r.s r.clock (ms 450)
  r.s.tickFrame (ms 466)
  checkEq "reveal: already visible moves nothing" (← st.value) 70
  checkEq "reveal: already visible never interrupts" (← st.mutationGen.get) gen
  -- Above the fold: top to the edge.
  st.scrollTo 200
  r.settle
  n.bringIntoView r.s
  advance r.s r.clock (ms 500)
  for i in [0:26] do
    r.s.tickFrame (ms (516 + 16 * i.toUInt64))
  checkEq "reveal above: minimal scroll, top to the edge" (← st.value) 150
  -- A wheel mid-reveal interrupts: the animation stands down.
  st.scrollTo 0
  r.settle
  n.bringIntoView r.s
  advance r.s r.clock (ms 1000)
  r.s.tickFrame (ms 1016)
  r.s.tickFrame (ms 1032)
  let _ ← r.im.pointerEvent (scrollAt 50 50 ⟨0, -1⟩)
  let atWheel ← st.value
  for i in [0:26] do
    r.s.tickFrame (ms (1048 + 16 * i.toUInt64))
  checkEq "reveal: a wheel mid-flight stands the animation down"
    (← st.value) atWheel

/-- A deep focusable inside two nested scrollables: both containers animate,
the outer seeing the bounds pre-compensated by the inner's upcoming shift. -/
private def bringIntoViewNested : IO Unit := do
  let outer ← ScrollState.create
  let inner ← ScrollState.create
  let r ← rig <| Box do
    Box (modifier := Modifier.size 100 100 |>.verticalScroll outer) do
      Column do
        leaf (Modifier.size 100 120)
        Box (modifier := Modifier.size 100 100 |>.verticalScroll inner) do
          Column do
            leaf (Modifier.size 100 130)
            leaf (Modifier.size 100 20 |>.focusable)
  checkEq "nested reveal: inner range" (← inner.maxValue) 50
  checkEq "nested reveal: outer range" (← outer.maxValue) 120
  check "nested reveal: tab focuses the deep target" (← r.im.keyEvent { key := .tab })
  let some n ← r.im.focus.focused | throw (IO.userError "nested reveal: nothing focused")
  n.bringIntoView r.s
  advance r.s r.clock (ms 1)
  for i in [0:26] do
    r.s.tickFrame (ms (16 + 16 * i.toUInt64))
  checkEq "nested reveal: the inner reveals within its viewport" (← inner.value) 50
  checkEq "nested reveal: the outer accounts for the inner's shift"
    (← outer.value) 120

/-- The Input group. -/
def run : IO Unit := do
  hitZOrder
  hitClipBounds
  hitWrapperOffsets
  consumptionBubbling
  scrollConsumption
  scrollAxisSplit
  hoverEnterExit
  hoverCursor
  tapGesture
  doubleTapGesture
  secondaryTapGesture
  longPressGesture
  dragGesture
  dragScrollSteals
  dragScrollFlingAndCatch
  dragScrollFlingEndStop
  dragScrollInnerDragWins
  dragScrollIgnoresSecondFinger
  nestedDragHandsOff
  nestedFlingHandoff
  nestedFlingNotAtStop
  nestedCrossAxis
  threeLevelCascade
  dispatchEndFinalizer
  dragRubberBand
  bounceOvershootThenSettle
  overscrollOptOut
  catchDuringBounce
  nestedBounceLandsOnOwner
  wheelNoBounce
  stretchDragAccumulates
  stretchReleaseSpringsBack
  stretchFlingAbsorb
  stretchCatchFreezes
  nestedStretchLandsOnOwner
  stretchModeRecordsWarpLayer
  bringIntoViewReveal
  bringIntoViewNested
  transformZoomFires
  transformStealsFromScrollable
  transformCancelDrops
  transformPinchEventRouting
  focusTraversal
  keyRouting
  textRouting
  clickableBehavior
  clickableDisabled
  clickableCancelResetsPressed
  clickableCancelMt
  multiTouchIndependentPresses
  multiTouchCancel
  mouseAndFingerCoexist
  pointerInputLifecycle
  missingScheduler
  raceSemantics
  sdlTranslation
  modalPopDetached
  focusDetachClears
  hoverCursorResync
  hoverAppearUnderCursor
  hoverDetachUnlatch

end Tests.Input
