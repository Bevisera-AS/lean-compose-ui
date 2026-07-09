import Compose
import ComposeTests.Harness
import ComposeTests.TestApplier

/-!
# DrawCache group (`test/ComposeTests/DrawCache.lean`)

The draw walk's per-node tessellation cache (`LayoutNode.cachedMesh`),
observed through `Draw.tessellationCount`: a static rounded box composed next
to an animating element must tessellate its background/border meshes once —
not once per rendered frame while the neighbor animates — and re-tessellate
exactly once when its resolved size changes. Pixel probes confirm the cached
path fills the same pixels as the uncached one.
-/

namespace Tests.DrawCache
open Compose Compose.Test Tests.Harness

private def staticShapeAcrossAnimation : IO Unit := do
  let target ← mutableStateOf (0 : Dp)   -- the neighbor's animated offset
  let side ← mutableStateOf (40 : Dp)    -- the static box's side length
  runComposeTest
    (content := Column {} (content := Tests.restartable 1 do
      -- The static shape: rounded background + rounded border = two meshes.
      Box (Modifier.testTag "static" |>.size (← side.get) (← side.get)
            |>.background Color.red (.rounded 8)
            |>.border 2 Color.blue (.rounded 8))
      -- The animating neighbor: a plain rectangular background (the crisp
      -- fillRect fast path — no tessellation) sliding on an animated offset,
      -- so every animation frame recomposes, remeasures it, and redraws the
      -- whole tree.
      let x ← animateDpAsState (← target.get) (.tween 200 0 .linear)
      Box (Modifier.offset (← x.get) 0 |>.size 20 20 |>.background Color.green)))
    do
      awaitIdle
      let t ← uiTest
      let c0 ← Draw.tessellationCount.get
      let f0 ← t.ctx.framesRendered.get
      check "cached mesh drew: static box interior is red"
        (colorNear (← pixel 20 20) 255 0 0)
      -- Drive the neighbor's 200 ms slide; every frame renders the full tree.
      target.set 100
      advanceTimeBy 240
      let frames := (← t.ctx.framesRendered.get) - f0
      check s!"animation rendered many frames ({frames})" (frames ≥ 5)
      checkEq "static shape did not re-tessellate during the animation"
        (← Draw.tessellationCount.get) c0
      check "static box interior still red after the animation"
        (colorNear (← pixel 20 20) 255 0 0)
      -- Resize the static box: both of its meshes rebuild — exactly once.
      side.set 60
      awaitIdle
      checkEq "resize re-tessellates exactly once per shape element"
        (← Draw.tessellationCount.get) (c0 + 2)
      check "resized box interior red (fresh mesh)"
        (colorNear (← pixel 30 30) 255 0 0)
      -- Steady state after the resize: cached again.
      advanceFrames 3
      checkEq "steady after resize: no further tessellation"
        (← Draw.tessellationCount.get) (c0 + 2)

/-- The DrawCache group. -/
def run : IO Unit := do
  scenario "mesh cache: static shapes tessellate once, not per frame"
    staticShapeAcrossAnimation

end Tests.DrawCache
