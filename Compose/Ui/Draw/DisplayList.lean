module

public import Compose.Ui.Draw.Tessellate
public meta import Compose.Ui.Draw.Tessellate
public import Compose.Ui.Draw.Image
public meta import Compose.Ui.Draw.Image
public import Sdl.Ttf.Text
public meta import Sdl.Ttf.Text

public section

/-!
# Display list (`Compose/Ui/Draw/DisplayList.lean`)

The backend-neutral rendering IR: a draw pass *records* a flat `DisplayList`
of self-contained primitives (`Compose/Ui/Draw/Scope.lean`), and a
`RenderBackend` *executes* it (`SdlBackend.lean` tessellates + rasterizes via
`SDL_Renderer`; the GPU backend renders shapes directly as SDF instances).

Recording resolves the ambient reader state — translation, clip intersection,
rounded clip, alpha — into a `PrimState` stamped on each primitive, so
executors need no transform/clip stack and each primitive is independently
replayable (golden-testable, and the seed of future damage tracking).

The SDL types here are the live `Sdl.Ttf.Text` handle a `TextRun` carries
(both backends draw text through SDL_ttf) and the `Sdl.Surface` inside an
`image`'s `ImageBitmap`; the module is free of `Sdl.Renderer` and `Sdl.Gpu`. There is no direct Compose analog — Compose
records into Skia's `Picture`/`DisplayListCanvas`; this list plays that role.
-/

namespace Compose.Draw

/-- Ambient drawing state resolved onto one primitive at record time. -/
structure PrimState where
  /-- Accumulated translation mapping the primitive's local coordinates to
  render-target pixels. -/
  origin : Offset := .zero
  /-- Resolved rectangular clip in render-target coordinates (`none` =
  unclipped); already the intersection of every enclosing `clipRect`. -/
  clip : Option Rect := none
  /-- Innermost enclosing rounded clip, in render-target coordinates. The GPU
  backend clips every primitive to it exactly; the SDL backend only applies
  the rectangular `clip` (its documented rounded-clip approximation). -/
  rounded : Option RoundRect := none
  /-- Accumulated alpha multiplier to fold into the primitive's colors. -/
  alpha : Float32 := 1.0
  deriving Repr, BEq, Inhabited

/-- A pixel effect applied to a layer's texture before it is composited.
Rendered by the GPU backend only (separable Gaussian render passes); the SDL
backend draws the content unblurred — a documented approximation, like its
rounded-clip story. Backdrop blur (sampling what's *behind* the layer) is out
of scope. -/
inductive LayerEffect where
  /-- No effect — the texture composites as rendered. -/
  | none
  /-- Gaussian blur with standard deviation `sigma` (device px). -/
  | blur (sigma : Float32)
  deriving Repr, BEq, Inhabited

namespace LayerEffect

/-- Canonical form for recording: a non-positive `sigma` is no effect, and
`sigma` caps at 16 (the GPU pass samples `3σ` texels per side; larger blurs
would want a downsample stage — deferred). -/
def normalize : LayerEffect → LayerEffect
  | .blur sigma => if sigma <= 0 then .none else .blur (min sigma 16)
  | .none => .none

/-- How far (px) the effect can spread content past its geometry: a Gaussian's
tails are negligible beyond `3σ` (+1 px AA). Inflates layer damage bounds and
the encoder's composite-region margin. -/
def spread : LayerEffect → Float32
  | .none => 0
  | .blur sigma => 3 * sigma + 1

#guard normalize (.blur 0) == .none
#guard normalize (.blur (-2)) == .none
#guard normalize (.blur 4) == .blur 4
#guard normalize (.blur 99) == .blur 16
#guard normalize .none == .none
#guard spread .none == 0
#guard spread (.blur 4) == 13

end LayerEffect

/-- Composite-time properties of an offscreen layer: the group alpha, an
optional affine transform, and a pixel effect — all applied once when the
layer's texture is composited (`transform` in render-target coordinates — the
layer-boundary transform model, like Compose's `graphicsLayer`; `effect`
processes the texture before the composite maps it). -/
structure LayerProps where
  /-- Group alpha applied once at composite. -/
  alpha : Float32 := 1
  /-- Composite transform (`none` = axis-aligned at the layer bounds). -/
  transform : Option Affine := none
  /-- Pixel effect on the layer texture (GPU-only; SDL renders unaffected). -/
  effect : LayerEffect := .none
  deriving Repr, BEq, Inhabited

/-- A recorded text run: the live `Ttf.Text` handle (backends draw through
it — it must not be mutated between record and execute, which holds because
both happen in the same frame on the main thread) plus the resolved paint.
`string` is for goldens/diagnostics only. -/
structure TextRun where
  /-- The live SDL text object (owned by the `TextLayout` that recorded it). -/
  text : Sdl.Ttf.Text
  /-- The shaped string (diagnostics; the handle is authoritative). -/
  string : String
  /-- The text color at record time (alpha folding happens at execute time
  from `PrimState.alpha`). -/
  color : Color

/-- Snap a text run's draw origin (plus the enclosing pass `shift`) to the
pixel grid. **Both backends** draw runs at this snapped origin: intra-run
subpixel layout is SDL_ttf's (preserved), the run as a whole lands on whole
pixels — so a given run rasterizes identically at any fractional origin
nearby (no shimmer) and fractional-origin text is byte-identical across
backends. Smooth fractional/rotated motion is a layer concern
(`Affine.snapComposite`). -/
def snapTextOrigin (origin shift : Offset) : Offset :=
  ⟨(origin.x + shift.x).round, (origin.y + shift.y).round⟩

-- Integer origins are fixed points (the static-parity invariant), .5 ties
-- round away from zero (`Float32.round`), and snapping commutes with the
-- integral shifts layer passes apply (regions snap to whole px).
#guard snapTextOrigin ⟨15, 41⟩ .zero == ⟨15, 41⟩
#guard snapTextOrigin ⟨15.4, 40.6⟩ .zero == ⟨15, 41⟩
#guard snapTextOrigin ⟨2.5, -2.5⟩ .zero == ⟨3, -3⟩
#guard snapTextOrigin ⟨15.4, 40.6⟩ ⟨3, -7⟩ == snapTextOrigin ⟨15.4, 40.6⟩ .zero + ⟨3, -7⟩

/-- One backend-neutral draw primitive. The draw origin for `rect`/`shape`/
`mesh` is `st.origin` plus the primitive's own local coordinates; a `text`
run's `st.origin` is the run's top-left directly. -/
inductive Prim where
  /-- A crisp axis-aligned solid fill (the no-tessellation fast path —
  `Renderer.fillRect` on SDL). Stored as top-left + size so executors pass
  the exact float extents through. -/
  | rect (st : PrimState) (color : Color) (topLeft : Offset) (size : Size)
  /-- An anti-aliased shape: the SDL backend rasterizes `cached` (tessellating
  the spec on `none` — the draw walk attaches its per-node cached mesh here);
  a GPU backend renders `spec` directly and ignores `cached`. -/
  | shape (st : PrimState) (spec : ShapeSpec) (cached : Option Mesh)
  /-- A pre-tessellated triangle mesh (no shape-level description — e.g. a
  `drawMesh` call from a `drawBehind` block). -/
  | mesh (st : PrimState) (m : Mesh)
  /-- A shaped text run drawn with its top-left at `st.origin`. -/
  | text (st : PrimState) (run : TextRun)
  /-- A bitmap draw: (a `src` portion of) `img` stretched onto `dst` (local
  coordinates). Executors resolve `img.id` through their texture caches. -/
  | image (st : PrimState) (img : ImageBitmap) (src : Option Rect) (dst : Rect)
      (sampling : Sampling)
  /-- An offscreen layer: `content` composited once with `props` (group
  alpha — fixing double-blending on backends with render-to-texture — and an
  optional affine transform; content renders axis-aligned into the layer at
  full quality, only the composite maps). `bounds` is the *content* region in
  render-target coordinates, pre-transform. The SDL backend flattens
  untransformed layers by folding the alpha into the content (the documented
  double-blend approximation) and renders transformed layers to a real
  offscreen target. -/
  | layer (st : PrimState) (bounds : Rect) (props : LayerProps) (content : Array Prim)

instance : Inhabited Prim := ⟨.mesh {} .empty⟩

/-- The ambient state stamped on a primitive. -/
def Prim.state : Prim → PrimState
  | .rect st .. | .shape st .. | .mesh st .. | .text st .. | .image st ..
  | .layer st .. => st

/-- A recorded frame: primitives in paint order (back to front). -/
abbrev DisplayList := Array Prim

/-! ## Golden projection -/

/-- Compact float formatting for goldens: integral values print without a
fractional part (`8` not `8.000000`). -/
def fmtF (x : Float32) : String :=
  let r := x.round
  if x == r && x.abs < 1e9 then toString r.toFloat.toInt64 else toString x

#guard fmtF 8 == "8"
#guard fmtF (-2) == "-2"
#guard fmtF 0.5 == toString (0.5 : Float32)

private def fmtOff (o : Offset) : String := s!"({fmtF o.x},{fmtF o.y})"

private def fmtRect (r : Rect) : String :=
  s!"({fmtF r.left},{fmtF r.top},{fmtF r.right},{fmtF r.bottom})"

private def fmtColor (c : Color) : String :=
  let (r, g, b, a) := c.toBytes
  let hex2 (v : UInt8) : String :=
    let digits := "0123456789abcdef".toList
    s!"{digits[(v.toNat / 16) % 16]!}{digits[v.toNat % 16]!}"
  s!"#{hex2 r}{hex2 g}{hex2 b}{hex2 a}"

#guard fmtColor .red == "#ff0000ff"
#guard fmtColor (Color.black.withAlpha 0.5) == "#00000080"

private def fmtRR (rr : RoundRect) : String :=
  s!"rr{fmtRect rr.rect}r{fmtF rr.topLeft.x}"

private def fmtRule : FillRule → String
  | .nonZero => "nonZero"
  | .evenOdd => "evenOdd"

/-- One-line golden form of a brush. -/
def Brush.brief : Brush → String
  | .solid c => fmtColor c
  | .linearGradient stops start stop => s!"grad[{stops.size}]{fmtOff start}→{fmtOff stop}"
  | .radialGradient stops center radius => s!"radial[{stops.size}]{fmtOff center} r={fmtF radius}"
  | .sweepGradient stops center startAngle =>
    s!"sweep[{stops.size}]{fmtOff center} a0={fmtF startAngle}"

/-- One-line golden form of a shape spec. -/
def ShapeSpec.brief : ShapeSpec → String
  | .rrFill rr b => s!"rrFill {fmtRR rr} {b.brief}"
  | .rrStroke rr w b => s!"rrStroke {fmtRR rr} w={fmtF w} {b.brief}"
  | .circleFill c r b => s!"circleFill c={fmtOff c} r={fmtF r} {b.brief}"
  | .circleFillClipped c r rr b => s!"circleFillClipped c={fmtOff c} r={fmtF r} {fmtRR rr} {b.brief}"
  | .circleStroke c r w b => s!"circleStroke c={fmtOff c} r={fmtF r} w={fmtF w} {b.brief}"
  | .arcStroke c r s0 s1 w b => s!"arcStroke c={fmtOff c} r={fmtF r} {fmtF s0}..{fmtF s1} w={fmtF w} {b.brief}"
  | .line p0 p1 w b => s!"line {fmtOff p0}→{fmtOff p1} w={fmtF w} {b.brief}"
  | .rrShadow rr off blur c => s!"rrShadow {fmtRR rr} off={fmtOff off} blur={fmtF blur} {fmtColor c}"
  | .pathFill p b =>
    s!"pathFill v={p.verbs.size} {fmtRect p.bounds} {fmtRule p.fillRule} {b.brief}"
  | .pathFillClipped p c b =>
    s!"pathFillClipped v={p.verbs.size} {fmtRect p.bounds} {fmtRule p.fillRule}"
      ++ s!" clip=v{c.verbs.size}{fmtRect c.bounds} {b.brief}"
  | .pathStroke p s b =>
    let cap := match s.cap with | .butt => "" | .round => " cap=round" | .square => " cap=square"
    let join := match s.join with | .miter => "" | .round => " join=round" | .bevel => " join=bevel"
    let dash := match s.dash with
      | some (ints, phase) => s!" dash=[{ints.size}]+{fmtF phase}"
      | none => ""
    s!"pathStroke v={p.verbs.size} {fmtRect p.bounds} w={fmtF s.width}{cap}{join}{dash} {b.brief}"

/-- One-line golden form of a primitive's ambient state (omitting defaults). -/
def PrimState.brief (st : PrimState) : String :=
  s!"@{fmtOff st.origin}"
    ++ (match st.clip with | some c => s!" clip={fmtRect c}" | none => "")
    ++ (match st.rounded with | some rr => s!" rounded={fmtRR rr}" | none => "")
    ++ (if st.alpha != 1.0 then s!" a={fmtF st.alpha}" else "")

/-- Golden projection of one primitive: one line per prim (layers nest their
content indented), live handles and mesh payloads elided (meshes print
vertex/triangle counts). Stable across runs — the IR test group asserts on
these lines. -/
partial def Prim.brief : Prim → String
  | .rect st color tl sz =>
    s!"rect {st.brief} {fmtColor color} tl={fmtOff tl} sz={fmtF sz.width}x{fmtF sz.height}"
  | .shape st spec cached =>
    s!"shape {st.brief} {spec.brief}{if cached.isSome then " cached" else ""}"
  | .mesh st m => s!"mesh {st.brief} v={m.vertexCount} t={m.triangleCount}"
  | .text st run => s!"text {st.brief} {fmtColor run.color} \"{run.string}\""
  | .image st img src dst sampling =>
    s!"image {st.brief} id={img.id} {img.width}x{img.height} dst={fmtRect dst}"
      ++ (match src with | some s => s!" src={fmtRect s}" | none => "")
      ++ (if sampling == .nearest then " nearest" else "")
  | .layer st bounds props content =>
    s!"layer {st.brief} bounds={fmtRect bounds} a={fmtF props.alpha}"
      ++ (match props.transform with
          | some t => s!" t=[{fmtF t.a},{fmtF t.b},{fmtF t.c},{fmtF t.d},{fmtF t.tx},{fmtF t.ty}]"
          | none => "")
      ++ (match props.effect with
          | .blur sigma => s!" blur={fmtF sigma}"
          | .none => "")
      ++ "\n"
      ++ String.intercalate "\n" (content.map (fun p => "  " ++ p.brief)).toList

#guard (Brush.radialGradient #[(0, .red), (1, .blue)] ⟨20, 20⟩ 10).brief
        == "radial[2](20,20) r=10"
#guard (Brush.sweepGradient #[(0, .red), (1, .blue)] ⟨20, 20⟩).brief
        == "sweep[2](20,20) a0=0"
#guard (Prim.rect {} .red ⟨0, 0⟩ ⟨10, 20⟩).brief == "rect @(0,0) #ff0000ff tl=(0,0) sz=10x20"
#guard (Prim.rect { origin := ⟨8, 8⟩, alpha := 0.5 } .red ⟨0, 0⟩ ⟨10, 20⟩).brief
        == s!"rect @(8,8) a={fmtF 0.5} #ff0000ff tl=(0,0) sz=10x20"
#guard (Prim.shape { clip := some ⟨0, 0, 40, 40⟩ }
          (.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .blue)) none).brief
        == "shape @(0,0) clip=(0,0,40,40) rrFill rr(0,0,40,40)r8 #0000ffff"
#guard (Prim.layer {} ⟨0, 0, 20, 20⟩ { effect := .blur 4 } #[.rect {} .red ⟨0, 0⟩ ⟨4, 4⟩]).brief
        == "layer @(0,0) bounds=(0,0,20,20) a=1 blur=4\n  rect @(0,0) #ff0000ff tl=(0,0) sz=4x4"

/-- All primitives (including layer content, recursively) satisfy `p` —
the well-formedness walker the IR test group uses. -/
partial def Prim.allWellFormed (p : Prim → Bool) : Prim → Bool
  | prim@(.layer _ _ _ content) => p prim && content.all (Prim.allWellFormed p)
  | prim => p prim

/-! ## Damage bounds -/

/-- Intersect conservative bounds with the primitive's resolved clip. -/
private def clipBounds (st : PrimState) (r : Rect) : Rect :=
  match st.clip with
  | some c => r.intersect c
  | none => r

/-- Conservative device-space damage bounds: `some r` = the primitive can only
touch pixels inside `r` (possibly degenerate when it draws nothing); `none` =
unknown extent (a text run — its size lives behind the live handle, so only an
enclosing clip bounds it). A layer reports its content's union: the SDL
flatten paints wherever the content does, and the GPU composite blends to a
no-op outside it. Damage-tracking groundwork — nothing consumes this
per-frame yet. -/
partial def Prim.bounds : Prim → Option Rect
  | .rect st _ topLeft size =>
    some (clipBounds st (Rect.ofOffsetSize (st.origin + topLeft) size))
  | .shape st spec _ => some (clipBounds st (spec.bounds.translate st.origin))
  | .mesh st m =>
    match m.bounds with
    | some b => some (clipBounds st (b.translate st.origin))
    | none => some .zero          -- no vertices: draws nothing
  | .text st _ => st.clip
  | .image st _ _ dst _ => some (clipBounds st (dst.translate st.origin))
  | .layer st _ props content => Id.run do
    let mut acc : Option Rect := none
    for p in content do
      match p.bounds with
      | none => return st.clip    -- unknown content extent
      | some b => acc := some ((acc.getD b).union b)
    -- An effect spreads pixels in the texture (pre-transform); a composite
    -- transform then maps where they land (AABB of the mapped union); the
    -- enclosing clip still bounds the composite.
    let u := (acc.getD .zero).inflate props.effect.spread
    return some (clipBounds st (match props.transform with
      | some t => t.mapRect u
      | none => u))

/-- Union damage bounds of a recorded frame: `some r` = the frame only touches
`r` (degenerate when nothing draws); `none` = unknown — repaint everything.
(`DisplayList` is an `abbrev`, so call this by name, not dot notation.) -/
def DisplayList.bounds (list : DisplayList) : Option Rect := Id.run do
  let mut acc : Option Rect := none
  for p in list do
    match p.bounds with
    | none => return none
    | some b => acc := some ((acc.getD b).union b)
  return some (acc.getD .zero)

#guard (Prim.rect { origin := ⟨5, 5⟩ } .red ⟨1, 1⟩ ⟨10, 10⟩).bounds == some ⟨6, 6, 16, 16⟩
#guard (Prim.rect { clip := some ⟨0, 0, 10, 10⟩ } .red ⟨5, 5⟩ ⟨20, 20⟩).bounds
        == some ⟨5, 5, 10, 10⟩
#guard (Prim.shape { origin := ⟨100, 0⟩ }
          (.rrFill (RoundRect.ofRect ⟨10, 10, 30, 30⟩) (.solid .red)) none).bounds
        == some ⟨109, 9, 131, 31⟩
#guard (Prim.mesh {} .empty).bounds == some .zero
#guard (Prim.layer {} ⟨0, 0, 50, 50⟩ { alpha := 0.5 } #[.rect {} .red ⟨10, 10⟩ ⟨20, 20⟩]).bounds
        == some ⟨10, 10, 30, 30⟩
#guard (Prim.layer {} ⟨0, 0, 50, 50⟩ { transform := some (.translation ⟨5, 0⟩) }
          #[.rect {} .red ⟨10, 10⟩ ⟨20, 20⟩]).bounds == some ⟨15, 10, 35, 30⟩
-- A blur spreads the content union by 3σ + 1 (pre-transform).
#guard (Prim.layer {} ⟨0, 0, 50, 50⟩ { effect := .blur 4 }
          #[.rect {} .red ⟨15, 15⟩ ⟨20, 20⟩]).bounds == some ⟨2, 2, 48, 48⟩
#guard (Prim.layer {} ⟨0, 0, 50, 50⟩
          { transform := some (.translation ⟨5, 0⟩), effect := .blur 1 }
          #[.rect {} .red ⟨10, 10⟩ ⟨20, 20⟩]).bounds == some ⟨11, 6, 39, 34⟩
#guard DisplayList.bounds #[.rect {} .red ⟨0, 0⟩ ⟨10, 10⟩, .rect {} .blue ⟨40, 40⟩ ⟨10, 10⟩]
        == some ⟨0, 0, 50, 50⟩
#guard DisplayList.bounds #[] == some .zero

end Compose.Draw

end
