import Compose.Animation.Animatable
import Compose.Runtime.LaunchedEffect

namespace Compose

/-!
# animate*AsState (`Compose/Animation/AnimateAsState.lean`)

Fire-and-forget value animation in composition, mirroring
`androidx.compose.animation.core.animateValueAsState` and its typed
wrappers: remember an `Animatable`, relaunch a coroutine whenever the
target changes (the old coroutine is cancelled by `LaunchedEffect`'s keying
— its already-parked frame continuation is dropped, so it never writes
again), and hand out the read-only `State` view of the animated value.

Deviation from Compose (minor): Compose funnels target changes through a
`Channel` inside one long-lived coroutine; keying `LaunchedEffect` on the
target is observably equivalent here because `Animatable.animateTo` carries
value and velocity across the interruption.
-/

/-- Animate toward `target` whenever it changes, starting from the current
value and velocity; returns the read-only animated value. Mirrors
`androidx.compose.animation.core.animateValueAsState`. -/
def animateValueAsState [BEq α] (target : α) (conv : VectorConverter α)
    (spec : AnimationSpec α := .spring) : Composable (State α) := do
  have : Nonempty α := ⟨target⟩
  let anim ← remember (Animatable.create target conv)
  LaunchedEffect target do
    -- Already resting at the target (e.g. the initial composition): no
    -- animation, no frame-clock subscription.
    let resting := (← anim.peek) == target && !(← anim.isRunning.cell.get)
    unless resting do
      anim.animateTo target spec
  return anim.value.asState

/-- `Float32` wrapper (visibility threshold `0.01`). Mirrors
`androidx.compose.animation.core.animateFloatAsState`. -/
def animateFloatAsState (target : Float32)
    (spec : AnimationSpec Float32 := .spring (visibilityThreshold := some 0.01)) :
    Composable (State Float32) :=
  animateValueAsState target .float32 spec

/-- `Dp` wrapper (visibility threshold `0.1.dp`). Mirrors
`androidx.compose.animation.core.animateDpAsState`. -/
def animateDpAsState (target : Dp)
    (spec : AnimationSpec Dp := .spring (visibilityThreshold := some ⟨0.1⟩)) :
    Composable (State Dp) :=
  animateValueAsState target .dp spec

/-- `Color` wrapper, animating sRGB channels (see `VectorConverter.color`
for the documented Oklab deviation). Mirrors
`androidx.compose.animation.animateColorAsState`. -/
def animateColorAsState (target : Color)
    (spec : AnimationSpec Color := .spring) : Composable (State Color) :=
  animateValueAsState target .color spec

/-- `Offset` wrapper (visibility threshold `0.5` px per axis). Mirrors
`androidx.compose.animation.core.animateOffsetAsState`. -/
def animateOffsetAsState (target : Offset)
    (spec : AnimationSpec Offset := .spring (visibilityThreshold := some ⟨0.5, 0.5⟩)) :
    Composable (State Offset) :=
  animateValueAsState target .offset spec

end Compose
