import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# Text test group (`test/ComposeTests/Text.lean`)

Exercises M7's text stack headless (dummy video driver, software renderer):
`FontStore` caching/resolution, `TextLayout` measure/wrap/caret geometry, and
the `Material.Text` composable end to end (glyph pixels, state-driven
re-render, wrapping, alignment). Reuses a bootstrapped `WindowContext`'s text
stack (`fontStore` + renderer `textEngine`) so `TextLayout`s draw through the
same software renderer the app loop uses.
-/

namespace Tests.Text
open Compose Tests.Harness

/-- Test config: software renderer for stable `readPixels`, no vsync. -/
private def cfg : AppConfig :=
  { vsync := false, rendererName := some Sdl.softwareRenderer, clearColor := .white }

/-- Bootstrap a small test window with `content`. -/
private def boot (content : Composable Unit) : IO WindowContext :=
  bootstrap "compose-text-test" 200 150 content cfg

/-- Whether an SDL pixel reads as "dark" (all RGB channels below mid). -/
private def isDark (c : Sdl.Color) : Bool :=
  c.r < 128 && c.g < 128 && c.b < 128

/-- Count dark pixels in the half-open box `[x0,x1) × [y0,y1)`. -/
private def countDark (surf : Sdl.Surface) (x0 x1 y0 y1 : Int32) : IO Nat := do
  let mut n := 0
  for y in [y0.toNatClampNeg : y1.toNatClampNeg] do
    for x in [x0.toNatClampNeg : x1.toNatClampNeg] do
      if isDark (← surf.readPixel (Int32.ofNat x) (Int32.ofNat y)) then
        n := n + 1
  return n

/-! ## FontStore -/

private def fontStore : IO Unit := do
  let store ← FontStore.create
  checkEq "fontstore: fresh cache empty" (← store.cacheSize) 0
  let _ ← store.resolve { fontSize := 14 } {}
  let _ ← store.resolve { fontSize := 14 } {}
  checkEq "fontstore: same style/density caches (one entry)" (← store.cacheSize) 1
  -- a different weight is a distinct entry
  let _ ← store.resolve { fontSize := 14, weight := .bold } {}
  checkEq "fontstore: distinct weight adds an entry" (← store.cacheSize) 2
  -- a different size is a distinct entry
  let _ ← store.resolve { fontSize := 20 } {}
  checkEq "fontstore: distinct size adds an entry" (← store.cacheSize) 3
  -- a different density (⇒ different px) is a distinct entry
  let _ ← store.resolve { fontSize := 14 } { density := 2 }
  checkEq "fontstore: distinct density adds an entry" (← store.cacheSize) 4
  -- rounding to the 0.5px step: 14sp and 14.02sp land in the same bucket
  let n ← store.cacheSize
  let _ ← store.resolve { fontSize := ⟨14.02⟩ } {}
  checkEq "fontstore: sub-step size reuses the bucket" (← store.cacheSize) n
  -- best-effort fallbacks: creation never throws on missing system fonts
  check "fontstore: create succeeded (fallbacks best-effort)" true

/-! ## TextLayout -/

private def textLayout (tc : TextContext) : IO Unit := do
  let mk (s : String) : IO TextLayout :=
    TextLayout.create tc.textEngine tc.fontStore s { fontSize := 16 } {}
  -- measure grows with content
  let a ← mk "hi"
  let b ← mk "hello world"
  let sa ← a.measure none
  let sb ← b.measure none
  check s!"textlayout: width grows with content ({sa.width} < {sb.width})" (sa.width < sb.width)
  check "textlayout: measured heights positive" (sa.height > 0 && sb.height > 0)
  -- empty string measures without crashing
  let e ← mk ""
  let se ← e.measure none
  check s!"textlayout: empty measures ({se.width}x{se.height})" (se.width == 0 || se.height ≥ 0)
  -- wrapping: a long line under a narrow bound is taller and ≤ the bound wide
  let w ← mk "the quick brown fox jumps over the lazy dog"
  let unwrapped ← w.measure none
  let wrapped ← w.measure (some 60)
  let lh ← w.lineHeight
  check s!"textlayout: wrapped ≤ bound wide ({wrapped.width} ≤ 60)" (wrapped.width ≤ 60)
  check s!"textlayout: wrapped taller ({wrapped.height} > {unwrapped.height})"
    (wrapped.height > unwrapped.height)
  check s!"textlayout: wrapped ≥ 2 lines ({wrapped.height} ≥ 2*{lh})"
    (wrapped.height ≥ 2 * lh)
  -- update with identical inputs does not touch the Ttf.Text
  let u ← mk "stable"
  let _ ← u.measure none
  let m0 ← u.mutationCount
  u.update "stable" { fontSize := 16 } {}
  checkEq "textlayout: no-op update leaves the Ttf.Text untouched" (← u.mutationCount) m0
  -- a real change does touch it, and the size follows
  u.update "stable and then some" { fontSize := 16 } {}
  check "textlayout: changed update touches the Ttf.Text" ((← u.mutationCount) > m0)
  let s1 ← u.measure none
  check "textlayout: measure reflects the new string" (s1.width > (← mk "stable" >>= (·.measure none)).width)

/-! ## Caret / hit geometry -/

private def caret (tc : TextContext) : IO Unit := do
  let t ← TextLayout.create tc.textEngine tc.fontStore "hello" { fontSize := 20 } {}
  let _ ← t.measure none
  -- byteOffsetToRect is monotone in x across offsets
  let mut lefts : Array Float32 := #[]
  for i in [0:5] do
    let r ← t.byteOffsetToRect i
    lefts := lefts.push r.left
  let mut monotone := true
  for i in [1:lefts.size] do
    if lefts[i]! < lefts[i-1]! then monotone := false
  check "caret: byteOffsetToRect left edges are monotone in x" monotone
  -- hitToByteOffset of each glyph's center returns that offset
  let mut roundtrips := 0
  for i in [0:5] do
    let r ← t.byteOffsetToRect i
    let off ← t.hitToByteOffset ⟨(r.left + r.right) / 2, (r.top + r.bottom) / 2⟩
    if off == i then roundtrips := roundtrips + 1
  check s!"caret: hit(center) round-trips the offset ({roundtrips}/5)" (roundtrips ≥ 4)

/-! ## Text composable, end to end -/

/-- Dark glyphs render on the white clear color, inside the text's box and not
outside it. -/
private def rendersGlyphs : IO Unit := do
  let ctx ← boot <| Text "Hello" (style := { fontSize := 24, color := .black })
  check "text: first step renders" (← step ctx cfg)
  let surf ← ctx.renderer.readPixels
  -- The Text node sits at the origin; its glyphs fall in the top-left band.
  let dark ← countDark surf 0 90 0 34
  check s!"text: dark glyph pixels in the text band ({dark})" (dark > 0)
  let bg ← surf.readPixel 170 130
  check s!"text: background outside the text is the clear color ({showColor bg})"
    (colorNear bg 255 255 255)

/-- A state-driven text change re-renders with changed coverage. -/
private def stateChangeRerenders : IO Unit := do
  let textState ← mutableStateOf "Hi"
  let ctx ← boot <| Tests.restartable 1 do
    let t ← textState.get
    Text t (style := { fontSize := 24, color := .black })
  let _ ← step ctx cfg
  let n1 ← countDark (← ctx.renderer.readPixels) 0 200 0 34
  check s!"text: initial string drew glyphs ({n1})" (n1 > 0)
  check "text: clean step renders nothing" (!(← step ctx cfg (idleCapMs := 10)))
  textState.set "Hello world wide"
  check "text: state write marks the frame dirty" (← ctx.needsFrame.get)
  check "text: dirty step re-renders" (← step ctx cfg)
  let n2 ← countDark (← ctx.renderer.readPixels) 0 200 0 34
  check s!"text: wider string changed the coverage ({n1} → {n2})" (n2 > n1)

/-- A long string in a narrow box wraps to multiple lines: the Text node grows
past two line heights. -/
private def wrapsInNarrowBox : IO Unit := do
  let long := "the quick brown fox jumps over the lazy dog"
  let ctx ← boot <|
    Box (Modifier.width 70) (content := fun _ =>
      Text long (style := { fontSize := 14, color := .black }))
  let _ ← step ctx cfg
  -- Navigate root → Box → Text and read the measured height.
  let boxNode ← ctx.root.child 0
  let textNode ← boxNode.child 0
  let sz ← textNode.size
  -- Compare against the font's natural line height at this density.
  let probe ← TextLayout.create ctx.textContext.textEngine ctx.textContext.fontStore
    long { fontSize := 14 } (← ctx.density)
  let lh ← probe.lineHeight
  check s!"text: wrapped node spans ≥ 2 lines ({sz.height} ≥ 2*{lh})" (sz.height ≥ 2 * lh)
  check s!"text: wrapped node stays within the box ({sz.width} ≤ 70)" (sz.width ≤ 70)

/-- Center-aligned text in a wide (fill) box leaves both margins clear and puts
glyphs near the center. -/
private def centerAlignment : IO Unit := do
  let ctx ← boot <|
    Text "Hi" (modifier := Modifier.fillMaxWidth)
      (style := { fontSize := 24, color := .black, align := .center })
  let _ ← step ctx cfg
  let surf ← ctx.renderer.readPixels
  let leftDark ← countDark surf 0 40 0 34
  let rightDark ← countDark surf 160 200 0 34
  let centerDark ← countDark surf 80 120 0 34
  check s!"align: left margin clear ({leftDark})" (leftDark == 0)
  check s!"align: right margin clear ({rightDark})" (rightDark == 0)
  check s!"align: glyphs near the center ({centerDark})" (centerDark > 0)

/-- The Text group. -/
def run : IO Unit := do
  fontStore
  -- The TextLayout/caret blocks need a renderer text engine; borrow one from a
  -- bootstrapped window's text stack.
  let ctx ← boot (pure ())
  textLayout ctx.textContext
  caret ctx.textContext
  rendersGlyphs
  stateChangeRerenders
  wrapsInNarrowBox
  centerAlignment

end Tests.Text
