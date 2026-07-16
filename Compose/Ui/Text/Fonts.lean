module

public import Std.Data.HashMap
public meta import Std.Data.HashMap
public import Compose.Ui.Text.Style
public meta import Compose.Ui.Text.Style
public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer
public import Sdl
public meta import Sdl

public section

namespace Compose

open Sdl.Ttf (Font)

/-!
# Font store (`Compose/Ui/Text/Fonts.lean`)

Resolves and caches `Ttf.Font` handles for the bundled Roboto family, keyed by
`(weight, device-px size)`. Mirrors the role of Compose's `FontFamily.Resolver`
(the piece that turns a `TextStyle` into a concrete, sized typeface).

- **Resolution**: the OFL-licensed Roboto files live in `assets/fonts/`. We
  look for them relative to the current directory first (demos and tests run
  from the repo root, per the lean-sdl3 convention), then relative to the
  executable, walking up a few levels — so an installed binary next to its
  assets still finds them. A missing family is an actionable error.
- **Caching**: fonts are opened lazily and memoized per `(weight, px)` with the
  px rounded to a `0.5`px step, in a `HashMap` behind an `IO.Ref`. `Ttf.init`
  runs once at store creation (SDL refcounts it).
- **Fallbacks**: platform system fonts are appended to every opened font via
  `Ttf.Font.addFallbackFont` for glyphs Roboto lacks. SDL_ttf does **not**
  retain fallbacks, so their handles are kept alive in the store. Missing
  system fonts are skipped (best effort).
-/

/-- Round a device-px size to the nearest `0.5`px cache step, as a positive
integer count of half-pixels (so `stepHalf/2` is the actual point size). -/
private def pxStepHalf (px : Float32) : Int32 := max 1 ((px * 2 + 0.5).floor.toInt32)

/-- Candidate directories that might hold the bundled font family: the current
directory, then the executable's directory walking up a few levels — each with
`assets/fonts` appended. -/
private def fontDirCandidates : IO (Array System.FilePath) := do
  let mut roots : Array System.FilePath := #[← IO.currentDir]
  let appDir ← try some <$> IO.appDir catch _ => pure none
  if let some d := appDir then
    let mut cur : System.FilePath := d
    for _ in [0:5] do
      roots := roots.push cur
      cur := cur.parent.getD cur
  return roots.map (· / "assets" / "fonts")

/-- The first candidate directory that contains `Roboto-Regular.ttf`, or an
actionable error naming where we looked. -/
private def resolveFontDir : IO System.FilePath := do
  let candidates ← fontDirCandidates
  for dir in candidates do
    if ← (dir / FontWeight.normal.fileName).pathExists then
      return dir
  throw <| IO.userError <|
    "Compose.FontStore: could not find the bundled font family " ++
    s!"({FontWeight.normal.fileName}); looked in: " ++
    String.intercalate ", " (candidates.map (·.toString)).toList

/-- Platform system fonts to append as fallbacks, in preference order (best
effort; missing files are skipped). -/
private def systemFallbackPaths : Array System.FilePath :=
  #["/System/Library/Fonts/Helvetica.ttc",
    "/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    -- Android system fonts (present on most devices; skipped elsewhere).
    "/system/fonts/NotoSansCJK-Regular.ttc",
    "/system/fonts/NotoColorEmoji.ttf"]

/-- Caches sized `Ttf.Font` handles for the bundled family and keeps the system
fallback fonts alive. Mirrors `androidx.compose.ui.text.font.FontFamily.Resolver`.
Create with `FontStore.create`; resolve a style with `FontStore.resolve`. -/
structure FontStore where
  /-- Directory holding the bundled `Roboto-*.ttf` files. -/
  dir : System.FilePath
  /-- Sized fonts keyed by `mixKeys weight.index stepHalf` (see `pxStepHalf`). -/
  cache : IO.Ref (Std.HashMap UInt64 Font)
  /-- Loaded system fallback fonts, held so SDL's non-retaining
  `addFallbackFont` references stay valid. -/
  fallbacks : Array Font

namespace FontStore

/-- Nominal point size the shared fallback fonts are opened at; fallbacks only
supply glyphs the bundled family lacks (rare), so a single fixed size is an
acceptable simplification. -/
private def fallbackPtSize : Float32 := 16

/-- Create a store: initialize SDL_ttf, locate the bundled family (in `dir`
when given — e.g. a platform launcher pointing at fonts unpacked from APK
assets — else by probing `fontDirCandidates`), and open the available system
fallback fonts (best effort). Mirrors constructing a `FontFamily.Resolver`. -/
def create (dir : Option System.FilePath := none) : IO FontStore := do
  Sdl.Ttf.init
  let dir ← match dir with
    | some d =>
      unless (← (d / FontWeight.normal.fileName).pathExists) do
        throw <| IO.userError <|
          s!"Compose.FontStore: {FontWeight.normal.fileName} not found in " ++
          s!"the configured font directory {d}"
      pure d
    | none => resolveFontDir
  let mut fallbacks : Array Font := #[]
  for p in systemFallbackPaths do
    if ← p.pathExists then
      match ← (try some <$> Sdl.Ttf.openFont p.toString fallbackPtSize catch _ => pure none) with
      | some f => fallbacks := fallbacks.push f
      | none => pure ()
  return { dir, cache := ← IO.mkRef ∅, fallbacks }

/-- The cache key for a `(weight, half-pixel size)` pair. -/
private def key (weight : FontWeight) (stepHalf : Int32) : UInt64 :=
  mixKeys weight.index stepHalf.toNatClampNeg.toUInt64

/-- Resolve `style` at `density` to a cached, sized `Ttf.Font`, opening it (and
attaching the fallbacks) on the first request for that `(weight, px-step)`.
`px = density.spToPx style.fontSize`. Mirrors resolving a `TextStyle` to a
platform typeface. -/
def resolve (store : FontStore) (style : TextStyle) (density : Density) : IO Font := do
  let stepHalf := pxStepHalf (density.spToPx style.fontSize)
  let k := key style.weight stepHalf
  if let some f := (← store.cache.get).get? k then
    return f
  let font ← Sdl.Ttf.openFont (store.dir / style.weight.fileName).toString (stepHalf.toFloat32 / 2)
  for fb in store.fallbacks do
    try font.addFallbackFont fb catch _ => pure ()
  store.cache.modify (·.insert k font)
  return font

/-- Number of distinct sized fonts currently cached (a probe for tests). -/
def cacheSize (store : FontStore) : IO Nat := return (← store.cache.get).size

end FontStore

end Compose

end
