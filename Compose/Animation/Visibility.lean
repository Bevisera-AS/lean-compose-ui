import Compose.Animation.Transition
import Compose.Runtime.Macro
import Compose.Ui.Layout

namespace Compose

/-!
# AnimatedVisibility (`Compose/Animation/Visibility.lean`)

Show/hide content with enter/exit animations, mirroring
`androidx.compose.animation.AnimatedVisibility`. This is the one animation
module that imports the UI layer (it emits a `Layout`).

`EnterTransition`/`ExitTransition` are combinable records (`++`, left
operand wins per effect, like Compose's `plus`): fade (alpha), slide
(offset by a fraction of the full size), expand/shrink (clipped, the
*reported* size is a fraction of the measured size, per axis).

The Compose `EnterExitState` machine (`PreEnter → Visible → PostExit`) maps
onto a single master fraction `f` animated by an `Animatable` (`0` = fully
hidden, `1` = fully shown) plus a composed-flag:
- *PreEnter*: content newly composed with `f = 0`, target `1`;
- *Visible*: `f` has settled at `1`;
- *PostExit*: `visible` turned false — **content stays composed** while `f`
  animates back to `0`, and only then leaves the composition.
Re-showing mid-exit interrupts with velocity carry-over and animates back
up from the current `f`.

Documented simplification vs. Compose: all effects of one transition are
driven by the single fraction and *one* spec (`EnterTransition.spec`, the
left-most combined one; default spring at `stiffnessMediumLow`), where
Compose animates each sub-effect with its own spec.
-/

/-- Enter effects for `AnimatedVisibility` (values describe the fully-hidden
end, `f = 0`). Combine with `++`. Mirrors
`androidx.compose.animation.EnterTransition`. -/
structure EnterTransition where
  /-- Initial alpha (`fadeIn`). -/
  fade : Option Float32 := none
  /-- Initial offset as fractions of the full size (`slideIn`). -/
  slideX : Option Float32 := none
  slideY : Option Float32 := none
  /-- Initial reported-width fraction (`expandHorizontally`). -/
  expandW : Option Float32 := none
  /-- Initial reported-height fraction (`expandVertically`). -/
  expandH : Option Float32 := none
  /-- Spec for the master fraction (first combined wins). -/
  spec : Option (AnimationSpec Float32) := none
  deriving Inhabited

/-- Exit effects for `AnimatedVisibility` (values describe the fully-hidden
end the content animates *toward*). Combine with `++`. Mirrors
`androidx.compose.animation.ExitTransition`. -/
structure ExitTransition where
  /-- Target alpha (`fadeOut`). -/
  fade : Option Float32 := none
  /-- Target offset as fractions of the full size (`slideOut`). -/
  slideX : Option Float32 := none
  slideY : Option Float32 := none
  /-- Target reported-width fraction (`shrinkHorizontally`). -/
  expandW : Option Float32 := none
  /-- Target reported-height fraction (`shrinkVertically`). -/
  expandH : Option Float32 := none
  /-- Spec for the master fraction (first combined wins). -/
  spec : Option (AnimationSpec Float32) := none
  deriving Inhabited

/-- Combine enter effects; the left operand wins where both define an
effect. Mirrors `EnterTransition.plus`. -/
instance : Append EnterTransition :=
  ⟨fun a b =>
    { fade := a.fade <|> b.fade, slideX := a.slideX <|> b.slideX
      slideY := a.slideY <|> b.slideY, expandW := a.expandW <|> b.expandW
      expandH := a.expandH <|> b.expandH, spec := a.spec <|> b.spec }⟩

/-- Combine exit effects; the left operand wins where both define an
effect. Mirrors `ExitTransition.plus`. -/
instance : Append ExitTransition :=
  ⟨fun a b =>
    { fade := a.fade <|> b.fade, slideX := a.slideX <|> b.slideX
      slideY := a.slideY <|> b.slideY, expandW := a.expandW <|> b.expandW
      expandH := a.expandH <|> b.expandH, spec := a.spec <|> b.spec }⟩

/-- Fade in from `initialAlpha`. Mirrors `androidx.compose.animation.fadeIn`. -/
def fadeIn (initialAlpha : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { fade := some initialAlpha, spec }

/-- Fade out to `targetAlpha`. Mirrors `androidx.compose.animation.fadeOut`. -/
def fadeOut (targetAlpha : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { fade := some targetAlpha, spec }

/-- Slide in horizontally from `initialOffsetX × width` px. Mirrors
`slideInHorizontally` (default: half the width, from the left). -/
def slideInHorizontally (initialOffsetX : Float32 := -0.5)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { slideX := some initialOffsetX, spec }

/-- Slide in vertically from `initialOffsetY × height` px. Mirrors
`slideInVertically` (default: half the height, from above). -/
def slideInVertically (initialOffsetY : Float32 := -0.5)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { slideY := some initialOffsetY, spec }

/-- Slide out horizontally to `targetOffsetX × width` px. Mirrors
`slideOutHorizontally`. -/
def slideOutHorizontally (targetOffsetX : Float32 := -0.5)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { slideX := some targetOffsetX, spec }

/-- Slide out vertically to `targetOffsetY × height` px. Mirrors
`slideOutVertically`. -/
def slideOutVertically (targetOffsetY : Float32 := -0.5)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { slideY := some targetOffsetY, spec }

/-- Expand (clipped) from `initialFraction` of the width. Mirrors
`expandHorizontally` (anchored top-left, no alignment parameter —
documented simplification). -/
def expandHorizontally (initialFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { expandW := some initialFraction, spec }

/-- Expand (clipped) from `initialFraction` of the height. Mirrors
`expandVertically`. -/
def expandVertically (initialFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { expandH := some initialFraction, spec }

/-- Expand from `initialFraction` of the full size on both axes. Mirrors
`expandIn`. -/
def expandIn (initialFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : EnterTransition :=
  { expandW := some initialFraction, expandH := some initialFraction, spec }

/-- Shrink (clipped) to `targetFraction` of the width. Mirrors
`shrinkHorizontally`. -/
def shrinkHorizontally (targetFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { expandW := some targetFraction, spec }

/-- Shrink (clipped) to `targetFraction` of the height. Mirrors
`shrinkVertically`. -/
def shrinkVertically (targetFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { expandH := some targetFraction, spec }

/-- Shrink to `targetFraction` of the full size on both axes. Mirrors
`shrinkOut`. -/
def shrinkOut (targetFraction : Float32 := 0.0)
    (spec : Option (AnimationSpec Float32) := none) : ExitTransition :=
  { expandW := some targetFraction, expandH := some targetFraction, spec }

/-- Default master-fraction spec when neither transition provides one:
Compose's visibility spring stiffness. -/
private def visibilityDefaultSpec : AnimationSpec Float32 :=
  .spring (stiffness := Spring.stiffnessMediumLow)

/-- Value of an effect channel at master fraction `f`, where `edge` is the
channel's value at the fully-hidden end (`none` = channel inactive, 1). -/
private def hiddenEdgeLerp (edge : Option Float32) (f : Float32) : Float32 :=
  match edge with
  | some e => e + (1.0 - e) * f
  | none => 1.0

#guard hiddenEdgeLerp (some 0.0) 0.0 == 0.0
#guard hiddenEdgeLerp (some 0.0) 0.25 == 0.25
#guard hiddenEdgeLerp (some 0.0) 1.0 == 1.0
#guard Easing.approx (hiddenEdgeLerp (some 0.4) 0.5) 0.7  -- half-way between edge 0.4 and 1
#guard hiddenEdgeLerp none 0.1 == 1.0

/-- Slide displacement at fraction `f` in px: `edge × (1−f) × full`. -/
private def slidePx (edge : Option Float32) (f full : Float32) : Float32 :=
  match edge with
  | some s => s * (1.0 - f) * full
  | none => 0.0

#guard slidePx (some (-0.5)) 0.0 100 == -50   -- fully hidden: half a size away
#guard slidePx (some (-0.5)) 0.5 100 == -25
#guard slidePx (some (-0.5)) 1.0 100 == 0     -- fully shown: in place
#guard slidePx none 0.3 100 == 0

/-- The animated wrapper around the content: its own restart scope, so the
per-frame fraction reads invalidate only this subtree. -/
composable def animatedVisibilityContent (anim : Animatable Float32)
    (entering : IO.Ref Bool) (enter : EnterTransition) (exit : ExitTransition)
    (modifier : Modifier) (content : Composable Unit) : Composable Unit := do
  let f ← anim.value.get
  let isEnter ← entering.get
  -- Resolve the active record's channels at the master fraction.
  let (fade, sx, sy, ew, eh) :=
    if isEnter then (enter.fade, enter.slideX, enter.slideY, enter.expandW, enter.expandH)
    else (exit.fade, exit.slideX, exit.slideY, exit.expandW, exit.expandH)
  let alpha := hiddenEdgeLerp fade f
  let wFrac := hiddenEdgeLerp ew f
  let hFrac := hiddenEdgeLerp eh f
  let m := if ew.isSome || eh.isSome then modifier.clip .rectangle else modifier
  let m := if fade.isSome then m.alpha alpha else m
  -- Slide displacement scales with the child's measured size, so it is
  -- applied inside the measure policy's placement (children measure with
  -- the incoming constraints — full size — like Compose's expand/shrink
  -- node; only the *reported* size is scaled).
  let sxE := (sx.map (fun s => s * (1.0 - f))).getD 0.0
  let syE := (sy.map (fun s => s * (1.0 - f))).getD 0.0
  Layout m
    (fun _ ms c => do
      let ps ← ms.mapM (·.measure c)
      let w := ps.foldl (fun acc p => max acc p.width) 0
      let h := ps.foldl (fun acc p => max acc p.height) 0
      return { size := c.constrain ⟨roundHalfUp (w.toFloat32 * wFrac),
                                    roundHalfUp (h.toFloat32 * hFrac)⟩
               placement := ps.forM (·.placeAt
                 ⟨roundHalfUp (w.toFloat32 * sxE), roundHalfUp (h.toFloat32 * syE)⟩) })
    content
    (policyInputs := some (mixKeys wFrac.toBits.toUInt64 (mixKeys hFrac.toBits.toUInt64
      (mixKeys sxE.toBits.toUInt64 syE.toBits.toUInt64))))

/-- Show/hide `content` with animated enter/exit transitions. The content
stays composed while the exit animation runs and leaves the composition
only once it completes; flipping `visible` back mid-exit reverses the
animation from the current position with carried velocity. Mirrors
`androidx.compose.animation.AnimatedVisibility`. -/
def AnimatedVisibility (visible : Bool) (modifier : Modifier := {})
    (enter : EnterTransition := fadeIn ++ expandVertically)
    (exit : ExitTransition := fadeOut ++ shrinkVertically)
    (content : Composable Unit := pure ()) : Composable Unit := do
  -- Content initially composed visible appears without an enter animation
  -- (Compose: `MutableTransitionState(initialState = visible)`).
  let anim ← remember (Animatable.create (if visible then (1.0 : Float32) else 0.0) .float32)
  let shown ← remember (mutableStateOf visible)
  let entering ← remember (IO.mkRef visible)
  liftM (m := IO) do
    entering.set visible
    if visible then shown.set true
  LaunchedEffect visible do
    if visible then
      unless (← anim.peek) == 1.0 && !(← anim.isRunning.cell.get) do
        anim.animateTo 1.0 (enter.spec.getD visibilityDefaultSpec)
    else if ← shown.cell.get then
      unless (← anim.peek) == 0.0 && !(← anim.isRunning.cell.get) do
        anim.animateTo 0.0 (exit.spec.getD visibilityDefaultSpec)
      -- Exit finished (an interrupting re-show cancels this coroutine
      -- before this line): remove the content from the composition.
      shown.set false
  if ← shown.get then
    withGroup 0x76697369 (animatedVisibilityContent anim entering enter exit modifier content)
  else
    withGroup 0x7669736f (pure ())

end Compose
