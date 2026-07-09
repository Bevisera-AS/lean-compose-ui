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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1 (logEvents log "under" (only := [.press])))
    leaf (Modifier.size 30 30 |>.pointerInput 2 (logEvents log "over" (only := [.press]))))
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
  let r ← rig <| Box {} (content := do
    Box (Modifier.size 40 40 |>.clip .circle |>.pointerInput 1 (logEvents log "self"))
      (content := do
        leaf (Modifier.fillMaxSize |>.pointerInput 2 (logEvents log "child")))
    pure ())
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.padding (all := 10)
      |>.pointerInput 1 (logEvents log "pad" (withPos := true))
      |>.size 30 30))
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
    Box (Modifier.size 50 50 |>.pointerInput 1
          (logEvents log "outer" (only := [.press, .release])))
      (content := do
        leaf (Modifier.size 50 50 |>.pointerInput 2
          (logEvents log "inner" (only := [.press, .release]) (consume := [.press]))))
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
    Box (Modifier.size 50 50 |>.onScroll (fun d => do outer.modify (·.push d); pure .zero))
      (content := do
        leaf (Modifier.size 50 50 |>.onScroll (fun d => do
          inner.modify (·.push d)
          return (if ← eat.get then d else .zero))))
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
    Box (Modifier.size 50 50 |>.onScroll (fun d => do outer.modify (·.push d); pure d))
      (content := do
        leaf (Modifier.size 50 50 |>.onScroll (fun d => pure ⟨0, d.y⟩)))
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
    Box (Modifier.size 100 80 |>.pointerInput 9 (logEvents log "p" ee))
      (content := do
        Row {} (content := do
          leaf (Modifier.size 50 50 |>.pointerInput 1 (logEvents log "a" ee))
          leaf (Modifier.size 50 50 |>.pointerInput 2 (logEvents log "b" ee))))
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
    Box (Modifier.size 100 80 |>.pointerHoverIcon .crosshair)
      (content := do
        Row {} (content := do
          leaf (Modifier.size 50 50 |>.pointerHoverIcon .text)
          leaf (Modifier.size 50 50)))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures (onTap := some fun p => taps.modify (·.push (p.x.toInt32, p.y.toInt32))))))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onDoubleTap := some fun _ => doubles.modify (· + 1)))))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onSecondaryTap := some fun p => secs.modify (·.push (p.x.toInt32, p.y.toInt32))))))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectTapGestures
        (onTap := some fun _ => taps.modify (· + 1))
        (onLongPress := some fun p => longs.modify (·.push (p.x.toInt32, p.y.toInt32)))
        (onPress := some fun ps => do
          pressed.modify (·.push true)
          let ok ← ps.tryAwaitRelease
          pressed.modify (·.push ok)))))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 50 50 |>.pointerInput 1
      (detectDragGestures
        (onDrag := fun p d =>
          log.modify (·.push s!"drag@{p.x.toInt32},{p.y.toInt32}Δ{d.x.toInt32},{d.y.toInt32}"))
        (onDragStart := fun p => log.modify (·.push s!"start@{p.x.toInt32},{p.y.toInt32}"))
        (onDragEnd := log.modify (·.push "end"))
        (onDragCancel := log.modify (·.push "cancel")))))
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
  let r ← rig <| Column {} (content := do
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "a"))
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "b"))
    leaf (Modifier.size 20 20 |>.focusable |>.onFocusChanged (fc "c")))
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
    Box (Modifier.size 100 100 |>.onKeyEvent (handler "anc" []))
      (content := do
        leaf (Modifier.size 20 20 |>.focusable |>.onKeyEvent (handler "leaf" [.a, .f]))
        leaf (Modifier.size 20 20 |>.focusable |>.onKeyEvent (handler "leaf2" [.tab])))
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
  let r ← rig <| Column {} (content := do
    leaf (Modifier.size 20 20 |>.focusable
      |>.onTextInput (fun t => do log.modify (·.push s!"a:{t}"); pure true))
    leaf (Modifier.size 20 20 |>.focusable
      |>.onTextInput (fun t => do log.modify (·.push s!"b:{t}"); pure true)))
  check "text: nothing focused, unhandled" (!(← r.im.textInput "x"))
  let _ ← r.im.keyEvent { key := .tab }
  check "text: focused node handles" (← r.im.textInput "hi")
  checkEq "text: delivered to the focused node only" (← log.get) #["a:hi"]

/-! ## clickable -/

/-- `Modifier.clickable`: mouse click fires, Enter/Space fire when focused,
disabled does nothing, and the interaction flags are observable while held /
hovered. -/
private def clickableBehavior : IO Unit := do
  let clicks ← IO.mkRef (0 : Nat)
  let srcCell ← IO.mkRef (none : Option InteractionSource)
  let r ← rig <| Box {} (content := do
    let src ← rememberInteractionSource
    SideEffect (srcCell.set (some src))
    leaf (Modifier.size 40 40 |>.clickable (clicks.modify (· + 1)) (source := some src)))
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
  let r ← rig <| Box {} (content := do
    leaf (Modifier.size 40 40 |>.clickable (clicks.modify (· + 1)) (enabled := false)))
  let _ ← r.im.pointerEvent (pressAt 10 10)
  let _ ← r.im.pointerEvent (releaseAt 10 10)
  checkEq "clickable: disabled ignores the mouse" (← clicks.get) 0
  let _ ← r.im.keyEvent { key := .tab }
  check "clickable: disabled is not focusable" ((← r.im.focus.focused).isNone)
  let _ ← r.im.keyEvent { key := .return }
  checkEq "clickable: disabled ignores the keyboard" (← clicks.get) 0

/-! ## pointerInput lifecycle -/

/-- The handler coroutine relaunches when the key changes (predecessor
cancelled first) and is cancelled when the node leaves the composition. -/
private def pointerInputLifecycle : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let key ← mutableStateOf (0 : UInt64)
  let show' ← mutableStateOf true
  let r ← rig <| Tests.restartable 1 do
    if ← show'.get then
      withGroup 11 <| Box {} (content := do
        let k ← liftM (m := IO) key.get
        leaf (Modifier.size 40 40 |>.pointerInput k
          (logEvents log s!"h{k}" (only := [.press, .release]))))
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
    (Box {} (content := do
      leaf (Modifier.size 50 50
        |>.clickable (clicks.modify (· + 1))
        |>.onScroll (fun d => do scrolls.modify (·.push d); pure d)
        |>.onTextInput (fun t => do texts.modify (·.push t); pure true))))
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
  let _ ← im.pointerEvent (moveTo 0 0)   -- keep `im` alive for the whole test
  (← ctx.composition).dispose

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
  focusTraversal
  keyRouting
  textRouting
  clickableBehavior
  clickableDisabled
  pointerInputLifecycle
  missingScheduler
  raceSemantics
  sdlTranslation

end Tests.Input
