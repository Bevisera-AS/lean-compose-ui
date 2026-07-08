namespace Compose

/-- An RGBA color in the sRGB color space, non-premultiplied, each channel in `[0, 1]`.

Mirrors `androidx.compose.ui.graphics.Color`. Channels are `Float32` to match
SDL's float color APIs (`SDL_FColor`). -/
structure Color where
  r : Float32
  g : Float32
  b : Float32
  a : Float32 := 1.0
  deriving Repr, BEq, Inhabited

namespace Color

private def clamp01 (v : Float32) : Float32 := min 1.0 (max 0.0 v)

/-- Build a color from 8-bit channel values. -/
def rgb8 (r g b : UInt8) (a : UInt8 := 255) : Color :=
  { r := r.toFloat32 / 255.0
    g := g.toFloat32 / 255.0
    b := b.toFloat32 / 255.0
    a := a.toFloat32 / 255.0 }

/-- Build a color from a packed `0xAARRGGBB` literal, the layout Compose uses:
`Color.hex 0xFF6200EE`. -/
def hex (argb : UInt32) : Color :=
  rgb8 (argb >>> 16).toUInt8 (argb >>> 8).toUInt8 argb.toUInt8 (argb >>> 24).toUInt8

/-- Return this color with a different alpha. -/
def withAlpha (c : Color) (a : Float32) : Color := { c with a }

/-- Convert to 8-bit channels (for SDL byte-color APIs). -/
def toBytes (c : Color) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let q (v : Float32) : UInt8 := (clamp01 v * 255.0 + 0.5).toUInt8
  (q c.r, q c.g, q c.b, q c.a)

/-- Linear interpolation between two colors (component-wise in sRGB, like
Compose's fast path). `t` is clamped to `[0, 1]`. -/
def lerp (x y : Color) (t : Float32) : Color :=
  let t := clamp01 t
  let f (a b : Float32) : Float32 := a + (b - a) * t
  { r := f x.r y.r, g := f x.g y.g, b := f x.b y.b, a := f x.a y.a }

/-- Source-over compositing of `fg` onto an opaque-or-not `bg`
(non-premultiplied inputs and output). -/
def compositeOver (fg bg : Color) : Color :=
  let a := fg.a + bg.a * (1.0 - fg.a)
  if a == 0.0 then { r := 0, g := 0, b := 0, a := 0 }
  else
    let f (cf cb : Float32) : Float32 := (cf * fg.a + cb * bg.a * (1.0 - fg.a)) / a
    { r := f fg.r bg.r, g := f fg.g bg.g, b := f fg.b bg.b, a }

def transparent : Color := { r := 0, g := 0, b := 0, a := 0 }
def black : Color := hex 0xFF000000
def white : Color := hex 0xFFFFFFFF
def red : Color := hex 0xFFFF0000
def green : Color := hex 0xFF00FF00
def blue : Color := hex 0xFF0000FF
def gray : Color := hex 0xFF888888
def lightGray : Color := hex 0xFFCCCCCC
def darkGray : Color := hex 0xFF444444
def yellow : Color := hex 0xFFFFFF00
def cyan : Color := hex 0xFF00FFFF
def magenta : Color := hex 0xFFFF00FF

#guard hex 0xFFFF0000 == { r := 1.0, g := 0.0, b := 0.0, a := 1.0 }
#guard (hex 0x80000000).a == (128 : UInt8).toFloat32 / 255.0
#guard (rgb8 255 0 0).toBytes == (255, 0, 0, 255)
#guard (lerp black white 0.0) == black
#guard (lerp black white 1.0) == white
#guard (lerp black white 2.0) == white
#guard (compositeOver (white.withAlpha 0.0) black) == black
#guard (compositeOver white black) == white
#guard (black.withAlpha 0.5).a == 0.5

end Color

end Compose
