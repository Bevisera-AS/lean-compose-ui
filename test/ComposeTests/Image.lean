import Compose
import ComposeTests.Harness

/-!
# Image group (`test/ComposeTests/Image.lean`)

Headless coverage for M-f images: the `createTextureFromSurface`-under-the-
dummy-driver assumption both backends' texture caches rest on, `ImageBitmap`
construction (`ofPixels` roundtrip, PNG decode of the committed
`assets/test/rgb2x2.png`), `drawImage` pixels through the SDL backend
(nearest-scaled quadrants, source rects, ambient alpha/clip), and the
recorded IR (brief goldens, damage bounds). `ContentScale.resolve` is
`#guard`-pinned in `Compose/Foundation/Image.lean`.
-/

namespace Tests.Image
open Compose Compose.Draw Compose.Draw.DrawScope Tests.Harness

private def mkRen (w h : Int32) : IO Sdl.Renderer := do
  let win ← Sdl.createWindow "compose-image" w h
  Sdl.createRenderer win (some Sdl.softwareRenderer)

private def clearBlack (ren : Sdl.Renderer) : IO Unit := do
  ren.setDrawColor 0 0 0 255
  ren.clear

/-- The 2×2 four-color test bitmap: red green / blue white. -/
private def quadColors : IO ImageBitmap :=
  ImageBitmap.ofPixels 2 2 fun x y =>
    match x, y with
    | 0, 0 => .red
    | 1, 0 => .green
    | 0, 1 => .blue
    | _, _ => .white

/-- Locate the committed test asset (current dir, then the executable's
ancestors — the font-resolution walk). -/
private def assetPath (rel : String) : IO (Option String) := do
  let mut roots : Array System.FilePath := #[← IO.currentDir]
  if let some d ← try some <$> IO.appDir catch _ => pure none then
    let mut cur := d
    for _ in [0:5] do
      roots := roots.push cur
      cur := cur.parent.getD cur
  for r in roots do
    if ← (r / rel).pathExists then
      return some (r / rel).toString
  return none

/-- The Image group. -/
def run : IO Unit := do
  Sdl.init .video

  -- 1. The headless assumption: createTextureFromSurface works under the
  -- dummy video driver's software renderer.
  do
    let ren ← mkRen 32 32
    clearBlack ren
    let surf ← Sdl.createSurface 2 2 .rgba32
    surf.writePixel 0 0 ⟨255, 0, 0, 255⟩
    surf.writePixel 1 0 ⟨0, 255, 0, 255⟩
    surf.writePixel 0 1 ⟨0, 0, 255, 255⟩
    surf.writePixel 1 1 ⟨255, 255, 255, 255⟩
    let tex ← ren.createTextureFromSurface surf
    tex.setScaleMode .nearest
    ren.texture tex none (some ⟨0, 0, 16, 16⟩)
    let shot ← ren.readPixels
    check "probe: texture-from-surface top-left quadrant"
      (colorNear (← shot.readPixel 4 4) 255 0 0)
    check "probe: texture-from-surface bottom-right quadrant"
      (colorNear (← shot.readPixel 12 12) 255 255 255)

  -- 2. ofPixels roundtrip: the bitmap is rgba32 with the written pixels
  do
    let img ← quadColors
    checkEq "ofPixels: width" img.width 2
    checkEq "ofPixels: height" img.height 2
    check "ofPixels: format is rgba32" ((← img.surface.format) == .rgba32)
    let p ← img.surface.readPixel 1 0
    check "ofPixels: pixel roundtrip" (p.r == 0 && p.g == 255 && p.b == 0 && p.a == 255)
    let a ← quadColors
    check "ImageBitmap: identity BEq (distinct ids)" (!(a == img) && img == img)

  -- 3. PNG decode of the committed asset
  do
    match ← assetPath "assets/test/rgb2x2.png" with
    | none => check "png: assets/test/rgb2x2.png found" false
    | some path =>
      let img ← ImageBitmap.load path
      checkEq "png: 2x2 decoded" (img.width, img.height) (2, 2)
      let p00 ← img.surface.readPixel 0 0
      let p11 ← img.surface.readPixel 1 1
      check "png: top-left red" (p00.r == 255 && p00.g == 0 && p00.b == 0)
      check "png: bottom-right white" (p11.r == 255 && p11.g == 255 && p11.b == 255)

  -- 4. nearest-scaled draw: exact quadrants at 20×
  do
    let ren ← mkRen 64 64
    clearBlack ren
    let img ← quadColors
    DrawScope.run ren {} do
      drawImage img ⟨0, 0, 40, 40⟩ (sampling := .nearest)
    let shot ← ren.readPixels
    check "draw: quadrant (10,10) red" (colorNear (← shot.readPixel 10 10) 255 0 0)
    check "draw: quadrant (30,10) green" (colorNear (← shot.readPixel 30 10) 0 255 0)
    check "draw: quadrant (10,30) blue" (colorNear (← shot.readPixel 10 30) 0 0 255)
    check "draw: quadrant (30,30) white" (colorNear (← shot.readPixel 30 30) 255 255 255)
    check "draw: outside dst untouched" (colorNear (← shot.readPixel 50 50) 0 0 0)

  -- 5. source rect: one pixel of the image stretched over the dst
  do
    let ren ← mkRen 32 32
    clearBlack ren
    let img ← quadColors
    DrawScope.run ren {} do
      drawImage img ⟨0, 0, 20, 20⟩ (src := some ⟨1, 0, 2, 1⟩) (sampling := .nearest)
    let shot ← ren.readPixels
    check "src: center all green" (colorNear (← shot.readPixel 10 10) 0 255 0)
    check "src: corner all green" (colorNear (← shot.readPixel 2 2) 0 255 0)

  -- 6. ambient state: translate + alpha fold + clip
  do
    let ren ← mkRen 64 64
    clearBlack ren
    let img ← ImageBitmap.ofPixels 2 2 fun _ _ => .white
    DrawScope.run ren {} do
      translate ⟨10, 10⟩ do
        clipRect ⟨0, 0, 20, 40⟩ do
          withAlpha 0.5 do
            drawImage img ⟨0, 0, 40, 40⟩ (sampling := .nearest)
    let shot ← ren.readPixels
    check "ambient: inside clip ≈ 50% white" (colorNear (← shot.readPixel 20 30) 128 128 128)
    check "ambient: right of clip untouched" (colorNear (← shot.readPixel 40 30) 0 0 0)
    check "ambient: untranslated origin untouched" (colorNear (← shot.readPixel 5 5) 0 0 0)

  -- 7. IR: brief golden and damage bounds
  do
    let img ← quadColors
    let (list, _) ← DrawScope.record {} do
      translate ⟨5, 5⟩ do
        clipRect ⟨0, 0, 20, 20⟩ do
          drawImage img ⟨0, 0, 40, 30⟩ (sampling := .nearest)
      drawImage img ⟨2, 2, 6, 6⟩ (src := some ⟨0, 0, 1, 1⟩)
    checkEq "image brief goldens" (list.map (·.brief)).toList
      [ s!"image @(5,5) clip=(5,5,25,25) id={img.id} 2x2 dst=(0,0,40,30) nearest"
      , s!"image @(0,0) id={img.id} 2x2 dst=(2,2,6,6) src=(0,0,1,1)" ]
    check "image bounds: dst ∩ clip" (list[0]!.bounds == some ⟨5, 5, 25, 25⟩)
    check "image bounds: unclipped dst" (list[1]!.bounds == some ⟨2, 2, 6, 6⟩)

  -- 8. premultipliedBytes: straight alpha × coverage, RGBA order
  do
    let img ← ImageBitmap.ofPixels 1 2 fun _ y =>
      if y == 0 then Color.red.withAlpha 0.5 else .green
    let bytes ← img.premultipliedBytes
    checkEq "premul: byte count" bytes.size 8
    check "premul: half-alpha red premultiplies r"
      (bytes.get! 0 == 128 && bytes.get! 1 == 0 && bytes.get! 3 == 128)
    check "premul: opaque green untouched"
      (bytes.get! 4 == 0 && bytes.get! 5 == 255 && bytes.get! 7 == 255)

end Tests.Image
