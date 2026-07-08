import Compose.Ui.Measure
import Compose.Core.Color
import Compose.Ui.Draw.Scope

namespace Compose

/-!
# Modifier chain (`Compose/Ui/Modifier.lean`)

`Modifier` is an ordered chain of elements folded (outermost first) into a
wrapper chain around a node's inner measurable, old-Compose
`LayoutNodeWrapper` style: each *layout* element transforms constraints on
the way down and size/placement on the way up; each *draw* element
contributes drawing before the content at its position in the chain. Mirrors
`androidx.compose.ui.Modifier`.

Pointer/focus/semantics elements arrive in M6 — `Modifier.Elem` is the
extension point (add constructors there and handle them in the node's
wrapper fold and hit-test walk).

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
  deriving Repr, BEq, Inhabited

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

/-- Structural equality; `drawBehind` blocks are never equal (function
payload), which conservatively re-draws them on every update — Compose's
capturing-lambda behavior. -/
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

/-- One element of a modifier chain. Mirrors `Modifier.Element`.
Extension points for later milestones (M6): `pointer`, `focus`, and
`semantics` constructors are added here and handled in
`LayoutNode`'s wrapper fold and the input hit-test walk. -/
inductive Modifier.Elem where
  | layout (e : LayoutElem)
  | draw (e : DrawElem)
  deriving BEq

/-- An ordered modifier chain, outermost element first. Mirrors
`androidx.compose.ui.Modifier` (the `then`-combined chain). -/
structure Modifier where
  elems : Array Modifier.Elem := #[]
  deriving BEq, Inhabited

namespace Modifier

/-- The empty modifier. Mirrors `Modifier` (the companion object). -/
def empty : Modifier := {}

/-- Concatenate two chains, `m` outermost. Mirrors `Modifier.then`. -/
def «then» (other : Modifier) (m : Modifier := {}) : Modifier :=
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

/-- Whether two chains are interchangeable *for measurement*: same length and,
position by position, equal layout elements (draw elements may differ — they
never affect geometry, so cached measurements and resolved draw indices stay
valid). Drives `needsRemeasure` vs `needsRedraw` on node update. -/
def layoutEq (a b : Modifier) : Bool :=
  a.elems.size == b.elems.size &&
  (a.elems.zip b.elems).all fun (x, y) =>
    match x, y with
    | .layout la, .layout lb => la == lb
    | .draw _, .draw _ => true
    | _, _ => false

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
        == (padding (all := 3)).elems ++ (size 1 2).elems
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

end Modifier

end Compose
