module

public import Compose.Animation.Visibility
public meta import Compose.Animation.Visibility
public import Compose.Foundation.Layouts
public meta import Compose.Foundation.Layouts

public section

namespace Compose

/-!
# AnimatedContent

Cross-fade (or any enter/exit pair) between contents keyed by a target
state — the screen-transition primitive: hold `inductive Screen` in a
`MutableState` and render it through `AnimatedContent`, and navigation
animates for free (`BackHandler` supplies the pops).

Implementation: a persistent entry list `(state, visible)`. Retargeting
marks the old entry exiting and adds/revives the target; every entry
renders stacked in a `Box` through `animatedVisibilityContent` (the
`AnimatedVisibility` engine) driven by a per-entry `Animatable` — stable
composition identity via `keyed`, so entries keep state and animation
progress across mid-flight reversals — and an entry leaves the list when
its exit animation completes.

Documented simplifications vs. `androidx.compose.animation.AnimatedContent`:
one enter/exit pair for all transitions (no per-target `transitionSpec`
lambda), and no `SizeTransform` — the container always sizes to the largest
live entry (screens fill their window anyway).
-/

/-- One `AnimatedContent` entry: its own enter/exit master fraction and the
direction flag `animatedVisibilityContent` resolves channels with. Composed
while visible *or* still exiting; removed when the exit settles (a reversal
mid-exit cancels the removal — `LaunchedEffect` relaunch semantics). -/
private def animatedContentEntry (visible : Bool) (firstPass : IO.Ref Bool)
    (enter : EnterTransition) (exit : ExitTransition) (onExited : IO Unit)
    (content : Composable Unit) : Composable Unit := do
  -- An entry composed on the container's first pass appears settled (like
  -- `AnimatedVisibility` content that starts visible); later entries start
  -- hidden and play the enter transition.
  let anim ← remember do
    Animatable.create (if (← firstPass.get) && visible then (1.0 : Float32) else 0.0)
      .float32
  let entering ← remember (IO.mkRef visible)
  liftM (m := IO) (entering.set visible)
  LaunchedEffect visible do
    if visible then
      unless (← anim.peek) == 1.0 && !(← anim.isRunning.cell.get) do
        anim.animateTo 1.0 (enter.spec.getD visibilityDefaultSpec)
    else
      unless (← anim.peek) == 0.0 && !(← anim.isRunning.cell.get) do
        anim.animateTo 0.0 (exit.spec.getD visibilityDefaultSpec)
      onExited
  animatedVisibilityContent anim entering enter exit {} content

/-- Animate between contents as `targetState` changes: the previous content
plays `exit` while the new one plays `enter` (both stay composed
mid-flight; rapid retargeting reverses animations with velocity carried).
`content` must be a pure function of the state. -/
def AnimatedContent [BEq α] [Hashable α] (targetState : α)
    (content : α → Composable Unit) (modifier : Modifier := {})
    (enter : EnterTransition := fadeIn) (exit : ExitTransition := fadeOut) :
    Composable Unit := do
  let entries ← remember (mutableStateOf (#[(targetState, true)] : Array (α × Bool)))
  let firstPass ← remember (IO.mkRef true)
  SideEffect (firstPass.set false)
  liftM (m := IO) do
    let es ← entries.cell.get
    unless es.any (fun e => e.1 == targetState && e.2) do
      entries.set <| Id.run do
        let es := es.map fun (s, v) => (s, v && s == targetState)
        match es.findIdx? (·.1 == targetState) with
        | some i => return es.set! i (targetState, true)
        | none => return es.push (targetState, true)
  let es ← entries.get
  Box (modifier := modifier) do
    for e in es do
      keyed e.1 do
        animatedContentEntry e.2 firstPass enter exit
          -- Exit settled: drop the entry — unless a retarget revived it
          -- (then it is visible again and must stay).
          (onExited := entries.modify (·.filter fun e' =>
            !(e'.1 == e.1 && !e'.2)))
          (content e.1)

end Compose

end
