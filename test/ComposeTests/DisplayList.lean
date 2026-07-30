import Compose
import ComposeTests.Harness

/-!
# DisplayList group (`test/ComposeTests/DisplayList.lean`)

The rendering IR: `DrawScope.record` runs a draw block with no backend and
returns the recorded `DisplayList`. Goldens over `Prim.brief` pin what each
draw op records and how ambient state (translation, clip intersection, rounded
clip, alpha) resolves onto primitives; well-formedness checks the invariants
every backend relies on; a composed-scene recording pins what the draw walk
emits (crisp rect fast path, cached shape specs, text runs). This group is the
GPU backend's headless coverage — both backends consume the identical list by
construction.
-/

namespace Tests.DisplayList
open Compose Compose.Draw Compose.Test Tests.Harness

/-- Record a draw block at density 1 and return the list. -/
private def rec (body : Draw.DrawM Unit) : IO Draw.DisplayList := do
  let (list, _) ← DrawScope.record {} body
  return list

/-- Golden-compare a recorded list's `brief` lines. -/
private def checkBriefs (name : String) (list : Draw.DisplayList) (want : List String) : IO Unit := do
  checkEq s!"{name}: prim count" list.size want.length
  for (p, w) in list.toList.zip want do
    checkEq s!"{name}: {w}" p.brief w

private def basicOps : IO Unit := do
  -- Solid fill records the crisp rect fast path; gradients and strokes record
  -- shape specs (tessellated by the executing backend).
  let l ← rec do
    DrawScope.drawRect (.solid .red) ⟨2, 3⟩ ⟨10, 20⟩
    DrawScope.drawRect (.solid .blue) ⟨0, 0⟩ ⟨5, 5⟩ (.stroke 2)
    DrawScope.drawCircle (.solid .green) ⟨50, 50⟩ 20
    DrawScope.drawLine (.solid .black) ⟨0, 0⟩ ⟨10, 10⟩ 2
  checkBriefs "basic ops" l
    [ "rect @(0,0) #ff0000ff tl=(2,3) sz=10x20"
    , "shape @(0,0) rrStroke rr(0,0,5,5)r0 w=2 #0000ffff"
    , "shape @(0,0) circleFill c=(50,50) r=20 #00ff00ff"
    , "shape @(0,0) line (0,0)→(10,10) w=2 #000000ff" ]
  -- drawRect on a solid brush must NOT tessellate; the others must.
  let c0 ← Draw.tessellationCount.get
  let _ ← rec (DrawScope.drawRect (.solid .red) ⟨0, 0⟩ ⟨10, 10⟩)
  checkEq "solid rect does not count a tessellation" (← Draw.tessellationCount.get) c0
  let _ ← rec (DrawScope.drawRoundRect (.solid .red) (RoundRect.circular ⟨0, 0, 10, 10⟩ 2))
  checkEq "shape draw counts one tessellation" (← Draw.tessellationCount.get) (c0 + 1)

private def ambientState : IO Unit := do
  -- Translation accumulates into origins; alpha multiplies; clips intersect
  -- in render-target coordinates.
  let l ← rec do
    DrawScope.translate ⟨10, 10⟩ do
      DrawScope.withAlpha 0.5 do
        DrawScope.clipRect ⟨0, 0, 30, 30⟩ do
          DrawScope.translate ⟨5, 0⟩ do
            DrawScope.clipRect ⟨0, 0, 100, 10⟩ do
              DrawScope.drawRect (.solid .red) ⟨1, 1⟩ ⟨4, 4⟩
  checkBriefs "nested state" l
    [ s!"rect @(15,10) clip=(15,10,40,20) a={Draw.fmtF 0.5} #ff0000ff tl=(1,1) sz=4x4" ]
  -- Rounded clip: rect clip to bounds + the rounded shape stamped in
  -- render-target coordinates on everything inside.
  let l ← rec do
    DrawScope.translate ⟨100, 0⟩ do
      DrawScope.clipRoundRect (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) do
        DrawScope.drawRect (.solid .blue) ⟨0, 0⟩ ⟨40, 40⟩
        DrawScope.drawCircle (.solid .red) ⟨20, 20⟩ 30
  checkBriefs "rounded clip" l
    [ "rect @(100,0) clip=(100,0,140,40) rounded=rr(100,0,140,40)r8 #0000ffff tl=(0,0) sz=40x40"
    , "shape @(100,0) clip=(100,0,140,40) rounded=rr(100,0,140,40)r8 \
       circleFillClipped c=(20,20) r=30 rr(0,0,40,40)r8 #ff0000ff" ]
  -- A `translate` between `clipRoundRect` and a shape-aware draw re-localizes
  -- the record-time clip shape: `circleFillClipped` pairs its center and rrect
  -- in the SAME (innermost) frame, so the clip lands where the rounded clip
  -- is on screen — not offset by the translation.
  let l ← rec do
    DrawScope.clipRoundRect (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) do
      DrawScope.translate ⟨5, 10⟩ do
        DrawScope.drawCircle (.solid .red) ⟨10, 10⟩ 6
  checkBriefs "translate re-localizes the rounded clip shape" l
    [ "shape @(5,10) clip=(0,0,40,40) rounded=rr(0,0,40,40)r8 \
       circleFillClipped c=(10,10) r=6 rr(-5,-10,35,30)r8 #ff0000ff" ]

private def layersAndShadows : IO Unit := do
  -- `withLayer` records a layer primitive wrapping its content, bounds in
  -- render-target coordinates; the layer's own alpha is NOT folded into the
  -- content (executors apply it once at composite).
  let l ← rec do
    DrawScope.translate ⟨10, 0⟩ do
      DrawScope.withLayer ⟨0, 0, 20, 20⟩ 0.5 do
        DrawScope.drawRect (.solid .red) ⟨1, 1⟩ ⟨4, 4⟩
  checkBriefs "layer" l
    [ s!"layer @(10,0) bounds=(10,0,30,20) a={Draw.fmtF 0.5}\n"
        ++ "  rect @(10,0) #ff0000ff tl=(1,1) sz=4x4" ]
  -- Full alpha records no layer at all.
  let l ← rec do
    DrawScope.withLayer ⟨0, 0, 10, 10⟩ 1.0 do
      DrawScope.drawRect (.solid .red) ⟨0, 0⟩ ⟨2, 2⟩
  checkBriefs "full-alpha layer elided" l
    [ "rect @(0,0) #ff0000ff tl=(0,0) sz=2x2" ]
  -- `withBlur` records a layer even at full alpha (the blur is the point);
  -- σ ≤ 0 records nothing; σ normalizes (caps at 16).
  let l ← rec do
    DrawScope.withBlur ⟨0, 0, 20, 20⟩ 4 do
      DrawScope.drawRect (.solid .red) ⟨1, 1⟩ ⟨4, 4⟩
    DrawScope.withBlur ⟨0, 0, 20, 20⟩ 0 do
      DrawScope.drawRect (.solid .blue) ⟨0, 0⟩ ⟨2, 2⟩
  checkBriefs "blur layer" l
    [ "layer @(0,0) bounds=(0,0,20,20) a=1 blur=4\n"
        ++ "  rect @(0,0) #ff0000ff tl=(1,1) sz=4x4"
    , "rect @(0,0) #0000ffff tl=(0,0) sz=2x2" ]
  -- The shadow spec records like any shape (SDL tessellates it, GPU renders
  -- the analytic form).
  let l ← rec do
    DrawScope.drawShape
      (.rrShadow (RoundRect.circular ⟨0, 0, 40, 40⟩ 8) ⟨0, 2⟩ 4 (Color.black.withAlpha 0.25))
  checkBriefs "shadow spec" l
    [ "shape @(0,0) rrShadow rr(0,0,40,40)r8 off=(0,2) blur=4 #00000040" ]

private def wellFormedness : IO Unit := do
  let (list, _) ← DrawScope.record {} do
    DrawScope.drawRoundRect (.solid .red) (RoundRect.circular ⟨0, 0, 40, 40⟩ 8)
    DrawScope.drawArc (.solid .blue) ⟨50, 50⟩ 20 0 3 4
    DrawScope.withAlpha 0.25 (DrawScope.drawMesh (Draw.roundRectFill (.circular ⟨0, 0, 9, 9⟩ 2) .red))
    DrawScope.drawMesh .empty   -- dropped, not recorded
  checkEq "empty meshes are not recorded" list.size 3
  let ok := list.all fun p => p.allWellFormed fun q =>
    let st := q.state
    (0 ≤ st.alpha && st.alpha ≤ 1)
    && (match st.clip with | some c => c.left ≤ c.right && c.top ≤ c.bottom | none => true)
    && (match q with
        | .shape _ spec cached => ((cached.map (·.mesh)).getD spec.tessellate).indicesInRange
            && cached.all fun pm => pm.idxBytes == pm.mesh.packIndices
        | .mesh _ m => m.indicesInRange
        | _ => true)
  check "recorded prims are well-formed (alpha in range, clips normalized, indices in range)" ok

private def damageBounds : IO Unit := do
  -- Recorded prims report conservative damage bounds (Prim.bounds): crisp
  -- rects exactly, shapes via ShapeSpec.bounds ∩ clip, layers via their
  -- content's union; the frame union covers everything drawn.
  let (list, _) ← DrawScope.record {} do
    DrawScope.translate ⟨10, 10⟩ do
      DrawScope.drawRect (.solid .red) ⟨0, 0⟩ ⟨20, 10⟩
    DrawScope.clipRect ⟨0, 0, 30, 30⟩ do
      DrawScope.drawCircle (.solid .blue) ⟨40, 20⟩ 15
    DrawScope.withLayer ⟨50, 50, 90, 90⟩ 0.5 do
      DrawScope.drawRect (.solid .green) ⟨60, 60⟩ ⟨10, 10⟩
  check "crisp rect bounds are its extent"
    (list[0]!.bounds == some ⟨10, 10, 30, 20⟩)
  check "shape bounds are the AA-inflated geometry ∩ clip"
    (list[1]!.bounds == some ⟨24, 4, 30, 30⟩)
  check "layer bounds are its content's union"
    (list[2]!.bounds == some ⟨60, 60, 70, 70⟩)
  check "frame union covers everything drawn"
    (Draw.DisplayList.bounds list == some ⟨10, 4, 70, 70⟩)

private def composedScene : IO Unit := do
  -- Record what the real draw walk emits for a small composed tree: a crisp
  -- rect for a plain background, a cached rrFill spec for a rounded one, and
  -- a text run.
  runComposeTest
    (Column do
      Box (modifier := Modifier.size 40 20 |>.background Color.red)
      Box (modifier := Modifier.size 40 40 |>.background Color.blue (.rounded 8))
      Text "hi" (color := some .black))
    do
      awaitIdle
      let t ← uiTest
      let density ← t.ctx.density
      let (list, _) ← DrawScope.record density t.ctx.root.drawTree
      let briefs := list.map (·.brief)
      check "plain background records the crisp rect fast path"
        (briefs.any (· == "rect @(0,0) #ff0000ff tl=(0,0) sz=40x20"))
      check "rounded background records a cached rrFill shape"
        (briefs.any (· == "shape @(0,20) rrFill rr(0,0,40,40)r8 #0000ffff cached"))
      check "text records a run with its resolved color"
        (briefs.any fun b => (b.startsWith "text @(0,60)") && b.endsWith "#000000ff \"hi\"")
      -- Recording is pure w.r.t. the backend: two records of the same tree
      -- yield the same briefs (cached meshes and all).
      let (list2, _) ← DrawScope.record density t.ctx.root.drawTree
      checkEq "re-recording the unchanged tree is stable"
        (list2.map (·.brief)).toList briefs.toList
  -- `Modifier.shadow` and `Modifier.alpha` through the real draw walk: an
  -- rrShadow spec (cached like any shape element) and a layer prim.
  runComposeTest
    (Column do
      Box (modifier := Modifier.size 40 20 |>.shadow 4 |>.background Color.red)
      Box (modifier := Modifier.size 20 10 |>.alpha 0.5 |>.background Color.blue))
    do
      awaitIdle
      let t ← uiTest
      let density ← t.ctx.density
      let (list, _) ← DrawScope.record density t.ctx.root.drawTree
      let briefs := list.map (·.brief)
      check "Modifier.shadow records a cached rrShadow spec"
        (briefs.any (· == "shape @(0,0) rrShadow rr(0,0,40,20)r0 off=(0,2) blur=4 #00000040 cached"))
      check "Modifier.alpha records a layer over the wrapper bounds"
        (briefs.any fun b =>
          b.startsWith s!"layer @(0,20) bounds=(0,20,20,30) a={Draw.fmtF 0.5}"
            && (b.splitOn "\n").any (·.trimAscii == "rect @(0,20) #0000ffff tl=(0,0) sz=20x10"))
  -- `Modifier.blur` through the real draw walk: a blur layer over the wrapper
  -- bounds with σ = radius/2 px (density 1 in tests).
  runComposeTest
    (Box (modifier := Modifier.blur 8 |>.size 30 20 |>.background Color.red))
    do
      awaitIdle
      let t ← uiTest
      let density ← t.ctx.density
      let (list, _) ← DrawScope.record density t.ctx.root.drawTree
      check "Modifier.blur records a blur layer over the wrapper bounds"
        ((list.map (·.brief)).any fun b =>
          b.startsWith "layer @(0,0) bounds=(0,0,30,20) a=1 blur=4"
            && (b.splitOn "\n").any (·.trimAscii == "rect @(0,0) #ff0000ff tl=(0,0) sz=30x20"))

private def brushModifiers : IO Unit := do
  -- `Modifier.backgroundBrush`/`borderBrush` through the real draw walk:
  -- unit-space gradients scale to the element size at draw time
  -- (`Brush.scaleTo`), recording cached rrFill/rrStroke shape specs.
  runComposeTest
    (Column do
      Box (modifier := Modifier.size 40 20
        |>.backgroundBrush (.gradient .black .white ⟨0, 0⟩ ⟨0, 1⟩) (.rounded 4))
      Box (modifier := Modifier.size 40 20
        |>.borderBrush 2 (.gradient .black .white ⟨0, 0⟩ ⟨0, 1⟩) (.rounded 4)))
    do
      awaitIdle
      let t ← uiTest
      let density ← t.ctx.density
      let (list, _) ← DrawScope.record density t.ctx.root.drawTree
      let briefs := list.map (·.brief)
      check "backgroundBrush records the size-scaled gradient rrFill"
        (briefs.any (· == "shape @(0,0) rrFill rr(0,0,40,20)r4 grad[2](0,0)→(0,20) cached"))
      check "borderBrush records the size-scaled gradient rrStroke just inside the bounds"
        (briefs.any (· == "shape @(0,20) rrStroke rr(1,1,39,19)r3 w=2 grad[2](0,0)→(0,20) cached"))

/-- The DisplayList group. -/
def run : IO Unit := do
  scenario "record: basic ops and the crisp-rect fast path" basicOps
  scenario "record: translation/clip/alpha resolve onto prims" ambientState
  scenario "record: layers and shadows" layersAndShadows
  scenario "record: well-formedness invariants" wellFormedness
  scenario "record: conservative damage bounds" damageBounds
  scenario "record: composed scene emits rects, cached shapes, text" composedScene
  scenario "record: brush modifiers scale unit-space gradients" brushModifiers

end Tests.DisplayList
