import Compose.Core.Geometry

namespace Compose

/-!
# Layout constraints (`Compose/Ui/Constraints.lean`)

Pure, SDL-free constraint arithmetic for the single-pass measure model,
mirroring `androidx.compose.ui.unit.Constraints`. All values are pixels
(`Int32`); an unbounded maximum is the `Constraints.infinity` sentinel
(`Int32` max, so plain `min`/`max` clamping treats it correctly).
-/

/-- Sentinel for an unbounded `maxWidth`/`maxHeight` (`Int32` max value).
Mirrors `Constraints.Infinity`. -/
def Constraints.infinity : Int32 := 2147483647

/-- Measurement constraints handed to a `Measurable`: the measured size must
satisfy `minWidth ≤ width ≤ maxWidth` and `minHeight ≤ height ≤ maxHeight`.
Mirrors `androidx.compose.ui.unit.Constraints`. -/
structure Constraints where
  minWidth : Int32 := 0
  maxWidth : Int32 := Constraints.infinity
  minHeight : Int32 := 0
  maxHeight : Int32 := Constraints.infinity
  deriving Repr, BEq, Inhabited

namespace Constraints

/-- Constraints that can only be satisfied by exactly `w × h`. Mirrors
`Constraints.fixed`. -/
def fixed (w h : Int32) : Constraints :=
  { minWidth := w, maxWidth := w, minHeight := h, maxHeight := h }

/-- Constraints with an exact width and unrestricted height. Mirrors
`Constraints.fixedWidth`. -/
def fixedWidth (w : Int32) : Constraints := { minWidth := w, maxWidth := w }

/-- Constraints with an exact height and unrestricted width. Mirrors
`Constraints.fixedHeight`. -/
def fixedHeight (h : Int32) : Constraints := { minHeight := h, maxHeight := h }

/-- Whether the maximum width is bounded (not `infinity`). Mirrors
`Constraints.hasBoundedWidth`. -/
def hasBoundedWidth (c : Constraints) : Bool := c.maxWidth != infinity

/-- Whether the maximum height is bounded (not `infinity`). Mirrors
`Constraints.hasBoundedHeight`. -/
def hasBoundedHeight (c : Constraints) : Bool := c.maxHeight != infinity

/-- Whether exactly one width satisfies the constraints. Mirrors
`Constraints.hasFixedWidth`. -/
def hasFixedWidth (c : Constraints) : Bool := c.minWidth == c.maxWidth

/-- Whether exactly one height satisfies the constraints. Mirrors
`Constraints.hasFixedHeight`. -/
def hasFixedHeight (c : Constraints) : Bool := c.minHeight == c.maxHeight

/-- Clamp a width into `[minWidth, maxWidth]`. Mirrors
`Constraints.constrainWidth`. -/
def constrainWidth (c : Constraints) (w : Int32) : Int32 :=
  min (max w c.minWidth) c.maxWidth

/-- Clamp a height into `[minHeight, maxHeight]`. Mirrors
`Constraints.constrainHeight`. -/
def constrainHeight (c : Constraints) (h : Int32) : Int32 :=
  min (max h c.minHeight) c.maxHeight

/-- Clamp a size into the constraints on both axes. Mirrors
`Constraints.constrain(IntSize)`. -/
def constrain (c : Constraints) (s : IntSize) : IntSize :=
  ⟨c.constrainWidth s.width, c.constrainHeight s.height⟩

/-- Coerce each bound of `other` to lie within `c`'s bounds (an unbounded
maximum in `other` becomes `c`'s maximum, staying unbounded only if `c` is).
Mirrors `Constraints.constrain(otherConstraints)`. -/
def constrainBounds (c other : Constraints) : Constraints :=
  { minWidth := c.constrainWidth other.minWidth
    maxWidth := c.constrainWidth other.maxWidth
    minHeight := c.constrainHeight other.minHeight
    maxHeight := c.constrainHeight other.maxHeight }

/-- Shift the constraints by `h`/`v` pixels (typically negative, to reserve
space for padding): minima floor at `0`, bounded maxima shift and floor at
`0`, `infinity` stays `infinity`. Mirrors `Constraints.offset`. -/
def offset (c : Constraints) (h v : Int32) : Constraints :=
  let addMax (m δ : Int32) : Int32 := if m == infinity then infinity else max 0 (m + δ)
  { minWidth := max 0 (c.minWidth + h)
    maxWidth := addMax c.maxWidth h
    minHeight := max 0 (c.minHeight + v)
    maxHeight := addMax c.maxHeight v }

/-- Drop the minimum bounds to `0`, keeping the maxima. Mirrors
`Constraints.copy(minWidth = 0, minHeight = 0)` / the layout-modifier
"loosen" idiom. -/
def loosen (c : Constraints) : Constraints := { c with minWidth := 0, minHeight := 0 }

/-- Whether `s` satisfies the constraints on both axes. Mirrors
`Constraints.isSatisfiedBy`. -/
def isSatisfiedBy (c : Constraints) (s : IntSize) : Bool :=
  c.minWidth <= s.width && s.width <= c.maxWidth &&
  c.minHeight <= s.height && s.height <= c.maxHeight

/-- Whether the constraints admit only the zero size on some axis. Mirrors
`Constraints.isZero`. -/
def isZero (c : Constraints) : Bool := c.maxWidth == 0 || c.maxHeight == 0

-- fixed / fixedWidth / fixedHeight
#guard fixed 10 20 == { minWidth := 10, maxWidth := 10, minHeight := 20, maxHeight := 20 }
#guard (fixed 10 20).hasFixedWidth && (fixed 10 20).hasFixedHeight
#guard (fixedWidth 10).hasFixedWidth && !(fixedWidth 10).hasFixedHeight
#guard (fixedWidth 10).maxHeight == infinity
#guard (fixedHeight 20).hasFixedHeight && !(fixedHeight 20).hasBoundedWidth
-- boundedness
#guard !(({} : Constraints).hasBoundedWidth) && !(({} : Constraints).hasBoundedHeight)
#guard ({ maxWidth := 100 : Constraints }).hasBoundedWidth
#guard !(({ maxWidth := 100 : Constraints }).hasBoundedHeight)
-- constrainWidth/Height clamp both directions; infinity max never clamps down
#guard ({ minWidth := 10, maxWidth := 100 : Constraints }).constrainWidth 5 == 10
#guard ({ minWidth := 10, maxWidth := 100 : Constraints }).constrainWidth 500 == 100
#guard ({ minWidth := 10, maxWidth := 100 : Constraints }).constrainWidth 50 == 50
#guard ({ minHeight := 10 : Constraints }).constrainHeight 500 == 500
#guard (({} : Constraints)).constrainWidth infinity == infinity
-- constrain (IntSize)
#guard (fixed 10 20).constrain ⟨100, 0⟩ == ⟨10, 20⟩
#guard ({ maxWidth := 50, maxHeight := 60 : Constraints }).constrain ⟨100, 100⟩ == ⟨50, 60⟩
#guard (({} : Constraints)).constrain ⟨7, 8⟩ == ⟨7, 8⟩
-- constrainBounds: fixed target clamped into incoming; unbounded stays via max
#guard ({ maxWidth := 100, maxHeight := 100 : Constraints }).constrainBounds (fixed 300 50)
        == { minWidth := 100, maxWidth := 100, minHeight := 50, maxHeight := 50 }
#guard (({} : Constraints)).constrainBounds (fixed 30 40) == fixed 30 40
#guard ({ minWidth := 20, maxWidth := 100 : Constraints }).constrainBounds {}
        == { minWidth := 20, maxWidth := 100 }
#guard ({ maxWidth := 100 : Constraints }).constrainBounds { minWidth := 10 }
        == { minWidth := 10, maxWidth := 100 }
-- offset: padding reservation shrinks; minima floor at 0; infinity preserved
#guard (fixed 100 80).offset (-20) (-10) == fixed 80 70
#guard ({ minWidth := 5, maxWidth := 30 : Constraints }).offset (-10) 0
        == { minWidth := 0, maxWidth := 20 }
#guard ({ maxWidth := 5 : Constraints }).offset (-10) 0 == { minWidth := 0, maxWidth := 0 }
#guard (({} : Constraints)).offset (-10) (-10) == ({} : Constraints)
#guard ({ minWidth := 10, maxWidth := 100 : Constraints }).offset 5 0
        == { minWidth := 15, maxWidth := 105 }
-- loosen
#guard (fixed 10 20).loosen == { maxWidth := 10, maxHeight := 20 }
#guard (({} : Constraints)).loosen == ({} : Constraints)
-- isSatisfiedBy
#guard (fixed 10 20).isSatisfiedBy ⟨10, 20⟩
#guard !(fixed 10 20).isSatisfiedBy ⟨10, 21⟩
#guard ({ minWidth := 5, maxWidth := 15 : Constraints }).isSatisfiedBy ⟨10, 0⟩
#guard !({ minWidth := 5, maxWidth := 15 : Constraints }).isSatisfiedBy ⟨4, 0⟩
#guard (({} : Constraints)).isSatisfiedBy ⟨2147483647, 0⟩
-- isZero
#guard ({ maxWidth := 0 : Constraints }).isZero
#guard !(fixed 1 1).isZero

end Constraints

end Compose
