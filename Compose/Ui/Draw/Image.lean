module

public import Compose.Core.Color
public meta import Compose.Core.Color
public import Compose.Core.Geometry
public meta import Compose.Core.Geometry
public import Sdl.Surface
public meta import Sdl.Surface

public section

/-!
# Image bitmaps (`Compose/Ui/Draw/Image.lean`)

`ImageBitmap` — decoded pixels ready to draw: an `Sdl.Surface` converted to
`rgba32` (straight alpha — SDL blits expect it; the GPU staging pass
premultiplies) with a process-unique `id` that keys both backends' texture
caches (`BEq` is handle identity, like Compose's `ImageBitmap`). Load BMP/PNG
files with `load`, or generate pixels with `ofPixels` (tests, demos).

Mirrors `androidx.compose.ui.graphics.ImageBitmap`; `Sampling` mirrors
`FilterQuality` (None/Low).
-/

namespace Compose.Draw

/-- Pixel sampling mode for scaled image draws. Mirrors Compose's
`FilterQuality.None`/`Low`. -/
inductive Sampling where
  /-- Nearest-neighbor (crisp pixel art, exact 1:1). -/
  | nearest
  /-- Bilinear filtering (the default). -/
  | linear
  deriving Repr, BEq, Inhabited

/-- Process-wide id source for `ImageBitmap` (texture-cache keys). -/
private initialize nextImageId : IO.Ref Nat ← IO.mkRef 0

/-- A decoded image: an `rgba32` (straight-alpha) surface plus its dimensions
and a process-unique cache id. Construct via `load` / `ofSurface` /
`ofPixels`. -/
structure ImageBitmap where private mk ::
  /-- Process-unique id — the texture-cache key on both backends. -/
  id : Nat
  /-- The pixels, always `rgba32` with straight alpha. -/
  surface : Sdl.Surface
  /-- Width in pixels. -/
  width : Nat
  /-- Height in pixels. -/
  height : Nat
  deriving Nonempty

/-- Handle identity, like Compose's `ImageBitmap` (same pixels loaded twice
compare unequal). -/
instance : BEq ImageBitmap := ⟨fun a b => a.id == b.id⟩

namespace ImageBitmap

/-- The image's natural size. -/
def size (img : ImageBitmap) : Size :=
  ⟨Float32.ofNat img.width, Float32.ofNat img.height⟩

/-- Wrap `surface` as an `ImageBitmap`, converting to `rgba32` (the surface is
copied unless already that format — the bitmap never aliases mutable caller
pixels in a different layout). -/
def ofSurface (surface : Sdl.Surface) : IO ImageBitmap := do
  let surface ← if (← surface.format) == .rgba32 then pure surface
                else surface.convert .rgba32
  let id ← nextImageId.modifyGet fun n => (n, n + 1)
  return { id, surface
           width := (← surface.width).toNatClampNeg
           height := (← surface.height).toNatClampNeg }

/-- Load a BMP or PNG image from a file (SDL auto-detects the format).
Throws an `IO` error on missing/undecodable files. -/
def load (path : String) : IO ImageBitmap := do
  ofSurface (← Sdl.loadSurface path)

/-- Generate a `w × h` bitmap from a pixel function (tests and demos — no
binary assets needed). -/
def ofPixels (w h : Nat) (f : Nat → Nat → Color) : IO ImageBitmap := do
  let surface ← Sdl.createSurface (Int32.ofNat w) (Int32.ofNat h) .rgba32
  for y in [0:h] do
    for x in [0:w] do
      let (r, g, b, a) := (f x y).toBytes
      surface.writePixel (Int32.ofNat x) (Int32.ofNat y) ⟨r, g, b, a⟩
  ofSurface surface

/-- The pixels as tightly-packed premultiplied RGBA bytes (the GPU staging
layout for `r8g8b8a8Unorm`). Correctness-first `readPixel` loop — one-time
per image at texture-cache miss; a bulk `Surface.pixels` binding upstream is
the noted fast-follow. -/
def premultipliedBytes (img : ImageBitmap) : IO ByteArray := do
  let mut out := ByteArray.emptyWithCapacity (img.width * img.height * 4)
  let premul (c a : UInt8) : UInt8 :=
    UInt8.ofNat ((c.toNat * a.toNat + 127) / 255)
  for y in [0:img.height] do
    for x in [0:img.width] do
      let c ← img.surface.readPixel (Int32.ofNat x) (Int32.ofNat y)
      out := out.push (premul c.r c.a) |>.push (premul c.g c.a)
        |>.push (premul c.b c.a) |>.push c.a
  return out

end ImageBitmap

end Compose.Draw

end
