import Compose.Ui.Measure
import Compose.Core.Color
import Compose.Ui.Draw.Scope
import Compose.Ui.Input.Pointer
import Compose.Ui.Input.Keyboard
import Compose.Ui.Semantics

namespace Compose

/-!
# Modifier chain (`Compose/Ui/Modifier.lean`)

`Modifier` is an ordered chain of elements folded (outermost first) into a
wrapper chain around a node's inner measurable, old-Compose
`LayoutNodeWrapper` style: each *layout* element transforms constraints on
the way down and size/placement on the way up; each *draw* element
contributes drawing before the content at its position in the chain. Mirrors
`androidx.compose.ui.Modifier`.

Non-layout constructors: pointer/focus elements landed in M6, semantics in
MT — `Modifier.Elem` is the extension point (add constructors there and
handle them in the node's wrapper fold and hit-test walk).

Combinators take the modifier they extend as a *trailing* default argument,
so both Compose spellings work:
`Modifier.padding (all := 16) |>.background Color.red |>.size 40 40`.

This module imports `Compose.Ui.Draw.Scope` (and therefore, transitively,
`Sdl`) solely because `Modifier.drawBehind` carries a `DrawM` block; no SDL
API is called outside the draw walk in `Compose.Ui.Layout`.
-/

/-- Round to the nearest integer, ties away from zero upward — Kotlin's
`Float.roundToInt`, used throughout Compose's layout math. -/
def roundHalfUp (x : Float32) : Int32 := (x + 0.5).floor.toInt32

#guard roundHalfUp 2.5 == 3
#guard roundHalfUp 2.4 == 2
#guard roundHalfUp (-2.5) == -2
#guard roundHalfUp (-2.6) == -3
#guard roundHalfUp 0 == 0

/-- A 2D alignment as horizontal/vertical biases in `[-1, 1]`
(`-1` = start/top, `0` = center, `1` = end/bottom). Mirrors
`androidx.compose.ui.Alignment` (`BiasAlignment`). -/
structure Alignment where
  horizontalBias : Float32
  verticalBias : Float32
  deriving Repr, BEq, Inhabited

/-- Horizontal-only alignment (Column cross axis). Mirrors
`Alignment.Horizontal`. -/
structure Alignment.Horizontal where
  bias : Float32
  deriving Repr, BEq, Inhabited

/-- Vertical-only alignment (Row cross axis). Mirrors `Alignment.Vertical`. -/
structure Alignment.Vertical where
  bias : Float32
  deriving Repr, BEq, Inhabited

namespace Alignment

def topStart : Alignment := ⟨-1, -1⟩
def topCenter : Alignment := ⟨0, -1⟩
def topEnd : Alignment := ⟨1, -1⟩
def centerStart : Alignment := ⟨-1, 0⟩
def center : Alignment := ⟨0, 0⟩
def centerEnd : Alignment := ⟨1, 0⟩
def bottomStart : Alignment := ⟨-1, 1⟩
def bottomCenter : Alignment := ⟨0, 1⟩
def bottomEnd : Alignment := ⟨1, 1⟩

def Horizontal.start : Horizontal := ⟨-1⟩
def Horizontal.centerHorizontally : Horizontal := ⟨0⟩
def Horizontal.«end» : Horizontal := ⟨1⟩

def Vertical.top : Vertical := ⟨-1⟩
def Vertical.centerVertically : Vertical := ⟨0⟩
def Vertical.bottom : Vertical := ⟨1⟩

/-- Horizontal alignments, `Alignment.start` spelling. -/
def start : Horizontal := .start
def centerHorizontally : Horizontal := .centerHorizontally
def «end» : Horizontal := .«end»

/-- Vertical alignments, `Alignment.top` spelling. -/
def top : Vertical := .top
def centerVertically : Vertical := .centerVertically
def bottom : Vertical := .bottom

/-- Offset of a `size`-px child inside `space` px for the given bias.
Mirrors `BiasAlignment`'s `align` (`(center * (1 + bias)).roundToInt()`). -/
def alignBias (bias : Float32) (size space : Int32) : Int32 :=
  roundHalfUp ((space - size).toFloat32 / 2 * (1 + bias))

/-- Position a `size` child inside `space`. Mirrors `Alignment.align`. -/
def align (a : Alignment) (size space : IntSize) : IntOffset :=
  ⟨alignBias a.horizontalBias size.width space.width,
   alignBias a.verticalBias size.height space.height⟩

/-- Position a child on the horizontal axis. Mirrors
`Alignment.Horizontal.align`. -/
def Horizontal.align (a : Horizontal) (size space : Int32) : Int32 :=
  alignBias a.bias size space

/-- Position a child on the vertical axis. Mirrors
`Alignment.Vertical.align`. -/
def Vertical.align (a : Vertical) (size space : Int32) : Int32 :=
  alignBias a.bias size space

#guard center.align ⟨10, 10⟩ ⟨100, 50⟩ == ⟨45, 20⟩
#guard topStart.align ⟨10, 10⟩ ⟨100, 50⟩ == ⟨0, 0⟩
#guard bottomEnd.align ⟨10, 10⟩ ⟨100, 50⟩ == ⟨90, 40⟩
#guard centerVertically.align 10 25 == 8      -- 7.5 rounds up
#guard bottom.align 10 25 == 15
#guard top.align 10 25 == 0
#guard center.align ⟨40, 0⟩ ⟨20, 0⟩ == ⟨-10, 0⟩ -- oversized content centers negatively

end Alignment

/-- The shape of a background/border/clip, resolved to a `RoundRect` at draw
time (radii are `Dp`, resolved against the ambient density). Mirrors
`androidx.compose.ui.graphics.Shape` (`RectangleShape` /
`RoundedCornerShape` / `CircleShape`). -/
inductive Shape where
  | rectangle
  | roundedCorners (topLeft topRight bottomRight bottomLeft : Dp)
  | circle
  deriving Repr, BEq, Inhabited

namespace Shape

/-- Uniform rounded corners. Mirrors `RoundedCornerShape(radius)`. -/
def rounded (radius : Dp) : Shape := .roundedCorners radius radius radius radius

/-- Resolve the shape to a `RoundRect` covering `⟨0, 0⟩ … size` (px), with
radii resolved via `density` and normalized so adjacent corners never
overlap. Mirrors `Shape.createOutline`. -/
def toRoundRect (s : Shape) (size : Size) (density : Density) : RoundRect :=
  match s with
  | .rectangle => .ofRect (Rect.ofSize size)
  | .roundedCorners tl tr br bl =>
    RoundRect.normalize
      { rect := Rect.ofSize size
        topLeft := .circular (density.dpToPx tl)
        topRight := .circular (density.dpToPx tr)
        bottomRight := .circular (density.dpToPx br)
        bottomLeft := .circular (density.dpToPx bl) }
  | .circle => RoundRect.circular (Rect.ofSize size) (min size.width size.height / 2)

#guard rectangle.toRoundRect ⟨40, 20⟩ {} == RoundRect.ofRect ⟨0, 0, 40, 20⟩
#guard (rounded 4).toRoundRect ⟨40, 20⟩ { density := 2 } == RoundRect.circular ⟨0, 0, 40, 20⟩ 8
#guard circle.toRoundRect ⟨40, 20⟩ {} == RoundRect.circular ⟨0, 0, 40, 20⟩ 10
-- normalization: radii larger than the sides are scaled down
#guard (rounded 30).toRoundRect ⟨40, 40⟩ {} == RoundRect.circular ⟨0, 0, 40, 40⟩ 20

end Shape

/-- The measure block of a `Modifier.customLayout` element: the generic
layout-modifier hook (M10, added for foundation's scroll containers). Given
the ambient density, the incoming constraints, and a `measureInner` function
that measures the rest of the wrapper chain (call it **exactly once** per
measure), it returns the wrapper's size and the offset at which the inner
content is placed. State reads inside run under the node's measure
observation, so reading e.g. a scroll offset here re-lays the node out when
it changes. Mirrors `androidx.compose.ui.layout.LayoutModifier.measure`
(with placement collapsed to an offset — our chain has no arbitrary
placement blocks). -/
structure CustomLayout where
  run : Density → Constraints → (Constraints → IO IntSize) → IO (IntSize × IntOffset)

/-- The identity block: measure inner with the incoming constraints, place at
the origin. -/
instance : Inhabited CustomLayout :=
  ⟨⟨fun _ c inner => do return (← inner c, .zero)⟩⟩

/-- A layout-affecting modifier element: transforms constraints downward and
size/placement upward in the wrapper chain. Mirrors the `LayoutModifier`
family (`PaddingModifier`, `SizeModifier`, `FillModifier`, …). -/
inductive LayoutElem where
  /-- Reserve space on each side. Mirrors `Modifier.padding`. -/
  | padding (left top right bottom : Dp)
  /-- Exact size on the given axes, clamped by the incoming constraints.
  Mirrors `Modifier.size`/`width`/`height` (enforce-incoming). -/
  | size (width height : Option Dp)
  /-- Bound the given constraint edges. Mirrors `Modifier.sizeIn`. -/
  | sizeIn (minWidth maxWidth minHeight maxHeight : Option Dp)
  /-- Exact size *overriding* the incoming constraints; the reported size is
  still coerced into them, centering overflowing content. Mirrors
  `Modifier.requiredSize`. -/
  | requiredSize (width height : Option Dp)
  /-- Fill a fraction of the bounded incoming maximum per axis. Mirrors
  `Modifier.fillMaxWidth`/`fillMaxHeight`/`fillMaxSize`. -/
  | fill (widthFraction heightFraction : Option Float32)
  /-- Measure content with loosened minima and align it inside the incoming
  bounds. Mirrors `Modifier.wrapContentSize`. -/
  | wrapContent (alignment : Alignment)
  /-- Displace content without affecting measurement. Mirrors
  `Modifier.offset`. -/
  | offset (x y : Dp)
  /-- Communicate data to the parent's measure policy (weight, Box align).
  Mirrors `ParentDataModifier`. -/
  | parentData (pd : ParentData)
  /-- Generic layout hook (see `CustomLayout`); compared by `key` — give the
  block a stable identity (hash of what it captures) so unchanged blocks
  don't invalidate measurement. Mirrors `Modifier.layout { ... }`. -/
  | custom (key : UInt64) (block : CustomLayout)
  deriving Inhabited

/-- Structural equality; `custom` compares by its identity key (the block is
a function). -/
instance : BEq LayoutElem where
  beq
    | .padding a b c d, .padding a' b' c' d' => a == a' && b == b' && c == c' && d == d'
    | .size w h, .size w' h' => w == w' && h == h'
    | .sizeIn a b c d, .sizeIn a' b' c' d' => a == a' && b == b' && c == c' && d == d'
    | .requiredSize w h, .requiredSize w' h' => w == w' && h == h'
    | .fill w h, .fill w' h' => w == w' && h == h'
    | .wrapContent a, .wrapContent a' => a == a'
    | .offset x y, .offset x' y' => x == x' && y == y'
    | .parentData p, .parentData p' => p == p'
    | .custom k _, .custom k' _ => k == k'
    | _, _ => false

#guard (LayoutElem.padding 1 2 3 4) == (LayoutElem.padding 1 2 3 4)
#guard (LayoutElem.padding 1 2 3 4) != (LayoutElem.padding 1 2 3 5)
#guard (LayoutElem.size (some 1) none) != (LayoutElem.sizeIn none (some 1) none none)
#guard (LayoutElem.custom 7 default) == (LayoutElem.custom 7 default)
#guard (LayoutElem.custom 7 default) != (LayoutElem.custom 8 default)

/-- A draw-affecting modifier element: contributes drawing at its wrapper's
coordinates, before the content. Mirrors the `DrawModifier` family. -/
inductive DrawElem where
  /-- Fill the wrapper bounds with `color` clipped to `shape`. Mirrors
  `Modifier.background`. -/
  | background (color : Color) (shape : Shape)
  /-- Stroke `shape` just inside the wrapper bounds. Mirrors
  `Modifier.border`. -/
  | border (width : Dp) (color : Color) (shape : Shape)
  /-- Clip the content (and everything inner) to `shape`. Mirrors
  `Modifier.clip`. -/
  | clip (shape : Shape)
  /-- Multiply the layer alpha for the content and everything inner. Mirrors
  `Modifier.alpha`. -/
  | alpha (a : Float32)
  /-- Arbitrary drawing behind the content at the wrapper's coordinates.
  Mirrors `Modifier.drawBehind`. -/
  | drawBehind (block : Draw.DrawM Unit)
  /-- Observe the wrapper's window-coordinate bounds. Executed by the draw
  walk (positions are final there), once per *rendered* frame — a documented
  deviation from Compose, which fires after placement; observably equivalent
  because anything consuming the rect schedules frames. Mirrors
  `Modifier.onGloballyPositioned`. -/
  | onPositioned (handler : Rect → IO Unit)

/-- Structural equality; `drawBehind` blocks and `onPositioned` handlers are
never equal (function payload), which conservatively re-draws them on every
update — Compose's capturing-lambda behavior. -/
instance : BEq DrawElem where
  beq
    | .background c s, .background c' s' => c == c' && s == s'
    | .border w c s, .border w' c' s' => w == w' && c == c' && s == s'
    | .clip s, .clip s' => s == s'
    | .alpha a, .alpha a' => a == a'
    | _, _ => false

#guard (DrawElem.background .red .rectangle) == (DrawElem.background .red .rectangle)
#guard (DrawElem.background .red .rectangle) != (DrawElem.background .blue .rectangle)
#guard (DrawElem.clip .circle) != (DrawElem.alpha 1)
#guard (DrawElem.drawBehind (pure ())) != (DrawElem.drawBehind (pure ()))

/-- A pointer-affecting modifier element: participates in hit testing at its
wrapper's region and receives the events dispatched along the hit path.
Mirrors the `PointerInputModifier` family. -/
inductive PointerElem where
  /-- A suspending pointer handler: (re)launched as a coroutine when the node
  enters the composition or `key` changes, cancelled when it leaves; events
  hitting the wrapper region are queued to it. Mirrors
  `Modifier.pointerInput(key) { ... }`. -/
  | input (key : UInt64) (handler : PointerInputScope → UiTask Unit)
  /-- System cursor while the pointer hovers the wrapper region (topmost
  hovered wins). Mirrors `Modifier.pointerHoverIcon`. -/
  | hoverIcon (cursor : Sdl.SystemCursor)
  /-- Wheel-scroll callback (delta in wheel ticks); `true` consumes. The
  raw-elem shortcut under foundation's scroll plumbing — mirrors
  `Modifier.scrollable`'s wheel handling, without the scroll state. -/
  | onScroll (handler : Offset → IO Bool)

/-- `input` compares by key (the coroutine's relaunch identity — Compose
semantics: the handler lambda is *not* an identity); `hoverIcon` by cursor;
`onScroll` never (capturing-lambda behavior). -/
instance : BEq PointerElem where
  beq
    | .input k _, .input k' _ => k == k'
    | .hoverIcon c, .hoverIcon c' => c == c'
    | _, _ => false

#guard (PointerElem.hoverIcon .text) == (PointerElem.hoverIcon .text)
#guard (PointerElem.hoverIcon .text) != (PointerElem.hoverIcon .pointer)
#guard (PointerElem.input 1 fun _ => pure ()) == (PointerElem.input 1 fun _ => pure ())
#guard (PointerElem.input 1 fun _ => pure ()) != (PointerElem.input 2 fun _ => pure ())
#guard (PointerElem.onScroll fun _ => pure false) != (PointerElem.onScroll fun _ => pure false)

/-- A focus/keyboard modifier element. Mirrors the `FocusModifier` +
`KeyInputModifier` families. -/
inductive FocusElem where
  /-- Makes the node a focus target (Tab traversal, click-to-focus). A chain
  is focusable iff it has a `focusable` element and none is disabled. Mirrors
  `Modifier.focusable(enabled)`. -/
  | focusable (enabled : Bool)
  /-- Observes this node gaining/losing focus. Mirrors
  `Modifier.onFocusChanged`. -/
  | onFocusChanged (handler : Bool → IO Unit)
  /-- Key handler; `true` consumes. Routed focused-node-first, then up the
  ancestor chain, then app fallbacks. Mirrors `Modifier.onKeyEvent`. -/
  | onKeyEvent (handler : KeyEvent → IO Bool)
  /-- Text-input (IME commit) handler; `true` consumes. Delivered to the
  focused node; marks the node a *text-input client* for the M11 IME hook
  (see `Compose.Ui.Input.Keyboard`). -/
  | onTextInput (handler : String → IO Bool)
  /-- IME composition (`textEditing`) handler: the composition text plus
  SDL's cursor `start`/`length` (codepoint-indexed); `true` consumes. Routed
  to the focused node like `onTextInput` (M11 addition). Mirrors the
  composition half of `BasicTextField`'s input session. -/
  | onTextEditing (handler : String → Int32 → Int32 → IO Bool)

/-- Only `focusable` carries comparable data; handler elements never compare
equal (capturing-lambda behavior). -/
instance : BEq FocusElem where
  beq
    | .focusable a, .focusable b => a == b
    | _, _ => false

#guard (FocusElem.focusable true) == (FocusElem.focusable true)
#guard (FocusElem.focusable true) != (FocusElem.focusable false)
#guard (FocusElem.onFocusChanged fun _ => pure ()) != (FocusElem.onFocusChanged fun _ => pure ())

/-- One element of a modifier chain. Mirrors `Modifier.Element`.
`layout` elements shape the wrapper chain; `draw`, `pointer`, `focus`, and
`semantics` elements never affect geometry — measurement resolves their
wrapper region (offset + size) for the draw walk and the input hit-test
walk; `semantics` elements carry the properties the MT test framework's
tree walk (`Compose.Test.Semantics`) reads. -/
inductive Modifier.Elem where
  | layout (e : LayoutElem)
  | draw (e : DrawElem)
  | pointer (e : PointerElem)
  | focus (e : FocusElem)
  | semantics (e : SemanticsProps)
  deriving BEq

/-- An ordered modifier chain, outermost element first. Mirrors
`androidx.compose.ui.Modifier` (the `then`-combined chain). -/
structure Modifier where
  elems : Array Modifier.Elem := #[]
  deriving BEq, Inhabited

namespace Modifier

/-- The empty modifier. Mirrors `Modifier` (the companion object). -/
def empty : Modifier := {}

/-- Concatenate two chains, the receiver outermost — `a.then b` (also
`a |>.then b`) puts `a`'s elements before `b`'s, exactly like Compose's
`a.then(b)`. (M9 fix: the parameter order used to bind the piped receiver to
the *inner* chain, silently reversing draw order.) Mirrors `Modifier.then`. -/
def «then» (m : Modifier) (other : Modifier) : Modifier :=
  ⟨m.elems ++ other.elems⟩

/-- Append a single element (innermost position). -/
def append (e : Elem) (m : Modifier := {}) : Modifier := ⟨m.elems.push e⟩

/-! ## Layout combinators -/

/-- Reserve `Dp` space around the content. Precedence: per-side (`left`…)
over per-axis (`horizontal`/`vertical`) over `all`. Mirrors
`Modifier.padding` (all overloads; `left`/`right` are physical, no RTL yet). -/
def padding (all : Dp := 0) (horizontal vertical left top right bottom : Option Dp := none)
    (m : Modifier := {}) : Modifier :=
  m.append (.layout (.padding
    (left.getD (horizontal.getD all)) (top.getD (vertical.getD all))
    (right.getD (horizontal.getD all)) (bottom.getD (vertical.getD all))))

/-- Exact preferred size, clamped by incoming constraints. Mirrors
`Modifier.size(width, height)`. -/
def size (width height : Dp) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.size (some width) (some height)))

/-- Exact preferred width. Mirrors `Modifier.width`. -/
def width (w : Dp) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.size (some w) none))

/-- Exact preferred height. Mirrors `Modifier.height`. -/
def height (h : Dp) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.size none (some h)))

/-- Constrain the size between the given bounds (omitted = unchanged).
Mirrors `Modifier.sizeIn`. -/
def sizeIn (minWidth maxWidth minHeight maxHeight : Option Dp := none)
    (m : Modifier := {}) : Modifier :=
  m.append (.layout (.sizeIn minWidth maxWidth minHeight maxHeight))

/-- Exact size regardless of incoming constraints (reported size is coerced;
overflowing content centers). Mirrors `Modifier.requiredSize`. -/
def requiredSize (width height : Dp) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.requiredSize (some width) (some height)))

/-- Fill `fraction` of the bounded incoming max width. Mirrors
`Modifier.fillMaxWidth`. -/
def fillMaxWidth (fraction : Float32 := 1.0) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.fill (some fraction) none))

/-- Fill `fraction` of the bounded incoming max height. Mirrors
`Modifier.fillMaxHeight`. -/
def fillMaxHeight (fraction : Float32 := 1.0) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.fill none (some fraction)))

/-- Fill `fraction` of the bounded incoming max size. Mirrors
`Modifier.fillMaxSize`. -/
def fillMaxSize (fraction : Float32 := 1.0) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.fill (some fraction) (some fraction)))

/-- Let the content measure to its own size and align it within the incoming
bounds. Mirrors `Modifier.wrapContentSize`. -/
def wrapContentSize (align : Alignment := .center) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.wrapContent align))

/-- Displace the content by `(x, y)` without affecting measurement. Mirrors
`Modifier.offset`. -/
def offset (x y : Dp) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.offset x y))

/-- Attach parent data (weight/align); the raw element behind
`RowScope.weight` and `BoxScope.align`. Mirrors `ParentDataModifier`. -/
def withParentData (pd : ParentData) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.parentData pd))

/-- Install a generic layout hook (see `CustomLayout`): `block` measures the
inner chain with constraints of its choosing (exactly once) and reports the
wrapper size plus the inner content's placement offset. `key` is the block's
identity for measurement invalidation (like `Layout`'s `policyInputs`).
The raw element behind foundation's `Modifier.verticalScroll`. Mirrors
`Modifier.layout { measurable, constraints -> ... }`. -/
def customLayout (key : UInt64) (block : CustomLayout) (m : Modifier := {}) : Modifier :=
  m.append (.layout (.custom key block))

/-! ## Draw combinators -/

/-- Fill the bounds with `color`, clipped to `shape`. Mirrors
`Modifier.background`. -/
def background (color : Color) (shape : Shape := .rectangle) (m : Modifier := {}) : Modifier :=
  m.append (.draw (.background color shape))

/-- Stroke `shape` just inside the bounds. Mirrors `Modifier.border`. -/
def border (width : Dp) (color : Color) (shape : Shape := .rectangle)
    (m : Modifier := {}) : Modifier :=
  m.append (.draw (.border width color shape))

/-- Clip content and children to `shape`. Mirrors `Modifier.clip`. -/
def clip (shape : Shape) (m : Modifier := {}) : Modifier :=
  m.append (.draw (.clip shape))

/-- Multiply the layer alpha for content and children. Mirrors
`Modifier.alpha`. -/
def alpha (a : Float32) (m : Modifier := {}) : Modifier :=
  m.append (.draw (.alpha a))

/-- Draw behind the content with full `DrawM` access. Mirrors
`Modifier.drawBehind`. -/
def drawBehind (block : Draw.DrawM Unit) (m : Modifier := {}) : Modifier :=
  m.append (.draw (.drawBehind block))

/-- Observe this element's wrapper bounds in **window coordinates** (render
px): `handler` runs once per rendered frame with the final rect — anchor
capture for `Popup`/`DropdownMenu`. Write the rect into a `mutableStateOf`
cell (structural equality) so unchanged positions don't schedule frames.
Mirrors `Modifier.onGloballyPositioned` (see `DrawElem.onPositioned` for the
draw-walk timing deviation). -/
def onGloballyPositioned (handler : Rect → IO Unit) (m : Modifier := {}) : Modifier :=
  m.append (.draw (.onPositioned handler))

/-! ## Pointer combinators -/

/-- Install a suspending pointer handler: launched as a coroutine when the
node enters the composition, relaunched when `key` changes (the predecessor
is cancelled first), cancelled when the node leaves. Pointer events whose
position hits this element's wrapper region are delivered through
`PointerInputScope.awaitEvent`, leaf→root along the hit path with
consumption. Mirrors `Modifier.pointerInput(key) { ... }`. -/
def pointerInput (key : UInt64) (handler : PointerInputScope → UiTask Unit)
    (m : Modifier := {}) : Modifier :=
  m.append (.pointer (.input key handler))

/-- Show `cursor` while the pointer hovers this element's region; the topmost
(leaf-most, innermost) hovered icon wins and the default cursor is restored
when nothing declares one. Mirrors `Modifier.pointerHoverIcon`. -/
def pointerHoverIcon (cursor : Sdl.SystemCursor) (m : Modifier := {}) : Modifier :=
  m.append (.pointer (.hoverIcon cursor))

/-- Handle wheel scrolls over this element (delta in wheel ticks, positive
`y` = away from the user); return `true` to consume. Mirrors the wheel
handling inside `Modifier.scrollable`. -/
def onScroll (handler : Offset → IO Bool) (m : Modifier := {}) : Modifier :=
  m.append (.pointer (.onScroll handler))

/-! ## Focus combinators -/

/-- Make the node a focus target: reachable by Tab/Shift-Tab traversal and
click-to-focus. Mirrors `Modifier.focusable(enabled)`. -/
def focusable (enabled : Bool := true) (m : Modifier := {}) : Modifier :=
  m.append (.focus (.focusable enabled))

/-- Observe this node gaining (`true`) / losing (`false`) focus. Mirrors
`Modifier.onFocusChanged`. -/
def onFocusChanged (handler : Bool → IO Unit) (m : Modifier := {}) : Modifier :=
  m.append (.focus (.onFocusChanged handler))

/-- Handle key events when this node (or a descendant) is focused; `true`
consumes and stops routing. Mirrors `Modifier.onKeyEvent`. -/
def onKeyEvent (handler : KeyEvent → IO Bool) (m : Modifier := {}) : Modifier :=
  m.append (.focus (.onKeyEvent handler))

/-- Handle committed text input when this node is focused; `true` consumes.
Also marks the node a text-input client for M11's IME lifecycle hook. Mirrors
the text-input routing of `BasicTextField`'s input modifier. -/
def onTextInput (handler : String → IO Bool) (m : Modifier := {}) : Modifier :=
  m.append (.focus (.onTextInput handler))

/-- Handle IME composition (`textEditing`) updates when this node is focused;
`true` consumes. The handler receives the composition text and SDL's
codepoint-indexed cursor `start`/`length` (M11 addition — see
`FocusElem.onTextEditing`). -/
def onTextEditing (handler : String → Int32 → Int32 → IO Bool)
    (m : Modifier := {}) : Modifier :=
  m.append (.focus (.onTextEditing handler))

/-! ## Semantics combinators -/

/-- Attach semantics properties for the MT test framework (and future
accessibility): what the node is (`role`), says (`text`, `desc`), and its
state (`disabled`/`toggled`/`selected`/`editableText`/`range`).
`mergeDescendants` folds descendant semantics into this node in the merged
tree (see `Compose.Test.Semantics`). Multiple semantics elements on one
chain combine with the outermost winning each stated field. Mirrors
`Modifier.semantics(mergeDescendants) { ... }`. -/
def semantics (testTag text desc editableText : Option String := none)
    (role : Option Semantics.Role := none)
    (disabled toggled selected : Option Bool := none)
    (range : Option Semantics.Range := none)
    (mergeDescendants : Bool := false) (m : Modifier := {}) : Modifier :=
  m.append (.semantics
    { testTag, text, contentDescription := desc, role, disabled, toggled
      selected, editableText, range, mergeDescendants })

/-- Tag the node with a test-only identity for `Matcher.tag` finders.
Mirrors `Modifier.testTag`. -/
def testTag (tag : String) (m : Modifier := {}) : Modifier :=
  m.semantics (testTag := some tag)

/-! ## Chain inspection -/

/-- Fold the chain's `parentData` elements (outer to inner; a later element
overrides the fields it sets). What `Measurable.parentData` exposes to the
parent policy. -/
def parentData (m : Modifier) : ParentData :=
  m.elems.foldl (init := {}) fun acc e =>
    match e with
    | .layout (.parentData pd) =>
      { weight := if pd.weight > 0 then pd.weight else acc.weight
        fill := if pd.weight > 0 then pd.fill else acc.fill
        align := pd.align <|> acc.align
        matchParentSize := acc.matchParentSize || pd.matchParentSize }
    | _ => acc

/-- Whether two chains are interchangeable *for measurement*: same length
and, position by position, equal layout elements (draw/pointer/focus/
semantics elements may differ — they never affect geometry, so cached
measurements and resolved element regions stay valid). Drives
`needsRemeasure` vs `needsRedraw` on node update. -/
def layoutEq (a b : Modifier) : Bool :=
  a.elems.size == b.elems.size &&
  (a.elems.zip b.elems).all fun (x, y) =>
    match x, y with
    | .layout la, .layout lb => la == lb
    | .draw _, .draw _ => true
    | .pointer _, .pointer _ => true
    | .focus _, .focus _ => true
    | .semantics _, .semantics _ => true
    | _, _ => false

/-- The chain's `pointerInput` elements as `(chain index, key, handler)`, in
chain order — what the reconcile pass (`LayoutNode.reconcilePointerInputs`)
matches positionally against the node's running coroutines. -/
def pointerInputElems (m : Modifier) :
    Array (Nat × UInt64 × (PointerInputScope → UiTask Unit)) := Id.run do
  let mut out := #[]
  for h : i in [0:m.elems.size] do
    if let .pointer (.input k f) := m.elems[i] then
      out := out.push (i, k, f)
  return out

/-- Whether the chain has a `focusable` element and none is disabled — the
node is then a focus target. Mirrors the merged enabled-state of stacked
`Modifier.focusable`s. -/
def focusEnabled (m : Modifier) : Bool :=
  m.elems.any (fun e => e matches .focus (.focusable true)) &&
  m.elems.all (fun e => !(e matches .focus (.focusable false)))

/-- Whether the chain has an `onTextInput` handler (a *text-input client*,
see the M11 IME hook in `Compose.Ui.Input.Keyboard`). -/
def isTextInputClient (m : Modifier) : Bool :=
  m.elems.any (fun e => e matches .focus (.onTextInput _))

/-- The chain's combined semantics: its `semantics` elements folded outer to
inner (outer wins each stated field); `none` when the chain has no semantics
element at all — the node is then invisible to the semantics tree. What
`Compose.Test.Semantics` reads per node. -/
def semanticsProps (m : Modifier) : Option SemanticsProps :=
  m.elems.foldl (init := none) fun acc e =>
    match e with
    | .semantics p =>
      match acc with
      | some outer => some (outer.combine p)
      | none => some p
    | _ => acc

-- padding resolution precedence
#guard (padding (all := 16)).elems == #[.layout (.padding 16 16 16 16)]
#guard (padding (horizontal := some 8)).elems == #[.layout (.padding 8 0 8 0)]
#guard (padding (all := 4) (vertical := some 8) (top := some 2)).elems
        == #[.layout (.padding 4 2 4 8)]
-- chaining appends innermost-last, both spellings
#guard (padding (all := 2) |>.background .red |>.size 10 10).elems
        == #[.layout (.padding 2 2 2 2), .draw (.background .red .rectangle),
             .layout (.size (some 10) (some 10))]
#guard («then» (size 1 2) (padding (all := 3))).elems
        == (size 1 2).elems ++ (padding (all := 3)).elems
#guard (size 1 2 |>.then (padding (all := 3))).elems
        == (size 1 2).elems ++ (padding (all := 3)).elems
-- parentData folding: later overrides, matchParentSize sticky
#guard (withParentData { weight := 2 } |>.withParentData { weight := 3, fill := false }).parentData
        == { weight := 3, fill := false }
#guard (withParentData { matchParentSize := true } |>.withParentData {}).parentData
        == { matchParentSize := true }
#guard (size 1 1).parentData == ({} : ParentData)
-- layoutEq: draw payloads don't affect it, layout params do
#guard layoutEq (padding (all := 2) |>.background .red) (padding (all := 2) |>.background .blue)
#guard !layoutEq (padding (all := 2)) (padding (all := 3))
#guard !layoutEq (padding (all := 2)) (padding (all := 2) |>.background .red)
#guard !layoutEq (background .red) (size 1 1)
-- pointer/focus elements are layout-inert but count as chain positions
#guard layoutEq (size 1 1 |>.pointerInput 1 fun _ => pure ())
                (size 1 1 |>.pointerInput 2 fun _ => pure ())
#guard !layoutEq (size 1 1) (size 1 1 |>.focusable)
#guard !layoutEq (size 1 1 |>.focusable) (size 1 1 |>.pointerHoverIcon .text)
-- chain inspection helpers
#guard ((padding (all := 2)).pointerInput 7 (fun _ => pure ())
          |>.pointerInputElems.map fun (i, k, _) => (i, k)) == #[(1, 7)]
#guard (size 1 1).pointerInputElems.isEmpty
#guard (focusable).focusEnabled
#guard !(focusable false).focusEnabled
#guard !(focusable |>.focusable false).focusEnabled
#guard !(padding (all := 1)).focusEnabled
#guard (onTextInput fun _ => pure true).isTextInputClient
#guard !(focusable).isTextInputClient
-- semantics: layout-inert, chain fold outer-wins, testTag shorthand
#guard layoutEq (size 1 1 |>.semantics (text := some "a"))
                (size 1 1 |>.semantics (text := some "b"))
#guard !layoutEq (size 1 1) (size 1 1 |>.testTag "t")
#guard (size 1 1).semanticsProps == none
#guard (testTag "t").semanticsProps == some { testTag := some "t" }
#guard (semantics (role := some .button)
          |>.padding (all := 2)
          |>.semantics (role := some .checkbox) (toggled := some true)).semanticsProps
        == some { role := some .button, toggled := some true }
#guard (semantics (mergeDescendants := true) |>.testTag "x").semanticsProps
        == some { testTag := some "x", mergeDescendants := true }

end Modifier

end Compose
