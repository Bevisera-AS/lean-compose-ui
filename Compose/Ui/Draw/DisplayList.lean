import Compose.Ui.Draw.Tessellate
import Sdl.Ttf.Text

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

The one SDL type here is the live `Sdl.Ttf.Text` handle a `TextRun` carries
(both backends draw text through SDL_ttf); the module is free of
`Sdl.Renderer` and `Sdl.Gpu`. There is no direct Compose analog — Compose
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
  /-- An offscreen layer: `content` composited once at `alpha` (fixes group
  opacity double-blending on backends with render-to-texture; the SDL
  backend flattens by folding `alpha` into the content — today's behavior).
  `bounds` is the composite region in render-target coordinates. Recorded
  from milestone M-c on; the constructor exists so the IR is stable. -/
  | layer (st : PrimState) (bounds : Rect) (alpha : Float32) (content : Array Prim)

instance : Inhabited Prim := ⟨.mesh {} .empty⟩

/-- The ambient state stamped on a primitive. -/
def Prim.state : Prim → PrimState
  | .rect st .. | .shape st .. | .mesh st .. | .text st .. | .layer st .. => st

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

/-- One-line golden form of a brush. -/
def Brush.brief : Brush → String
  | .solid c => fmtColor c
  | .linearGradient stops start stop => s!"grad[{stops.size}]{fmtOff start}→{fmtOff stop}"

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
    let rule := match p.fillRule with | .nonZero => "nonZero" | .evenOdd => "evenOdd"
    s!"pathFill v={p.verbs.size} {fmtRect p.bounds} {rule} {b.brief}"

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
  | .layer st bounds alpha content =>
    s!"layer {st.brief} bounds={fmtRect bounds} a={fmtF alpha}\n"
      ++ String.intercalate "\n" (content.map (fun p => "  " ++ p.brief)).toList

#guard (Prim.rect {} .red ⟨0, 0⟩ ⟨10, 20⟩).brief == "rect @(0,0) #ff0000ff tl=(0,0) sz=10x20"
#guard (Prim.rect { origin := ⟨8, 8⟩, alpha := 0.5 } .red ⟨0, 0⟩ ⟨10, 20⟩).brief
        == s!"rect @(8,8) a={fmtF 0.5} #ff0000ff tl=(0,0) sz=10x20"
#guard (Prim.shape { clip := some ⟨0, 0, 40, 40⟩ }
          (.rrFill (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) (.solid .blue)) none).brief
        == "shape @(0,0) clip=(0,0,40,40) rrFill rr(0,0,40,40)r8 #0000ffff"

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
  | .layer st _ _ content => Id.run do
    let mut acc : Option Rect := none
    for p in content do
      match p.bounds with
      | none => return st.clip    -- unknown content extent
      | some b => acc := some ((acc.getD b).union b)
    return some (clipBounds st (acc.getD .zero))

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
#guard (Prim.layer {} ⟨0, 0, 50, 50⟩ 0.5 #[.rect {} .red ⟨10, 10⟩ ⟨20, 20⟩]).bounds
        == some ⟨10, 10, 30, 30⟩
#guard DisplayList.bounds #[.rect {} .red ⟨0, 0⟩ ⟨10, 10⟩, .rect {} .blue ⟨40, 40⟩ ⟨10, 10⟩]
        == some ⟨0, 0, 50, 50⟩
#guard DisplayList.bounds #[] == some .zero

end Compose.Draw
