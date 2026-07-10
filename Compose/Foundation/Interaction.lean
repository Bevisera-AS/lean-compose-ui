import Compose.Foundation.Gestures
import Compose.Ui.Modifier
import Compose.Runtime.Composer
import Compose.Runtime.Macro

namespace Compose

/-!
# Interaction sources and `clickable` (`Compose/Foundation/Interaction.lean`)

`InteractionSource` exposes a widget's pressed/hovered/focused flags as
`MutableState`s, so Material state layers (M9) recompose exactly when a flag
flips — the flag-shaped condensation of
`androidx.compose.foundation.interaction.MutableInteractionSource`'s
interaction streams (a documented simplification: no per-interaction
objects; `collectIsPressedAsState` and friends become plain state reads).

`Modifier.clickable` is the M9 widget workhorse: tap gesture (press
interaction + `onClick`) + hover interaction + focusability + keyboard
activation (Enter/Space when focused) + a pointer cursor. Mirrors
`androidx.compose.foundation.clickable`.
-/

/-- Observable pressed/hovered/focused flags. Reads recompose the reader when
the flag flips (they are `MutableState`s). `id` keys the input coroutines of
`Modifier.hoverable`/`clickable`, so swapping sources relaunches them. -/
structure InteractionSource where
  /-- Identity for coroutine relaunch keys. -/
  id : UInt64
  /-- A press is held on the widget. -/
  pressed : MutableState Bool
  /-- The pointer hovers the widget. -/
  hovered : MutableState Bool
  /-- The widget has keyboard focus. -/
  focused : MutableState Bool

instance : Nonempty InteractionSource :=
  ⟨{ id := 0
     pressed := Classical.choice inferInstance
     hovered := Classical.choice inferInstance
     focused := Classical.choice inferInstance }⟩

namespace InteractionSource

/-- Fresh source, all flags down. Mirrors `MutableInteractionSource()`. -/
def create : IO InteractionSource :=
  return { id := (← freshId).toUInt64
           pressed := ← MutableState.create false
           hovered := ← MutableState.create false
           focused := ← MutableState.create false }

end InteractionSource

/-- Remember an `InteractionSource` at this composition position. Mirrors
`remember { MutableInteractionSource() }`. -/
def rememberInteractionSource : Composable InteractionSource :=
  remember InteractionSource.create

namespace Modifier

/-- Track pointer hover on `source.hovered` (enter → `true`, exit →
`false`). Mirrors `Modifier.hoverable(interactionSource, enabled)`. -/
def hoverable (source : InteractionSource) (enabled : Bool := true)
    (m : Modifier := {}) : Modifier :=
  m.pointerInput (mixKeys (stringKey "Compose.Modifier.hoverable")
                    (mixKeys source.id (if enabled then 1 else 0)))
    (detectHover
      (onEnter := fun _ => if enabled then source.hovered.set true else pure ())
      (onExit := source.hovered.set false))

/-- Make the node clickable: tap gesture (`onClick` on a completed click),
press/hover/focus interactions on `source`, focusability, keyboard activation
(Enter/Space/keypad-Enter while focused), and the pointer (hand) cursor.
Disabled, it handles nothing and leaves the focus order. Mirrors
`androidx.compose.foundation.clickable(interactionSource, enabled, onClick)`.

The gesture coroutine relaunches when `enabled` or the source identity
changes (they are part of its key); like Compose, the `onClick` lambda itself
is not an identity — pass the current state through `MutableState`s rather
than swapping lambdas. -/
def clickable (onClick : IO Unit) (enabled : Bool := true)
    (source : Option InteractionSource := none) (m : Modifier := {}) : Modifier :=
  let key := mixKeys (stringKey "Compose.Modifier.clickable")
    (mixKeys (match source with | some s => s.id | none => 0)
             (if enabled then 1 else 0))
  let setPressed (b : Bool) : IO Unit :=
    match source with
    | some s => s.pressed.set b
    | none => pure ()
  let hovered := match source with
    | some s => m.hoverable s enabled
    | none => m
  hovered
  |>.pointerHoverIcon (if enabled then .pointer else .default)
  -- Semantics: clickables merge their descendants (a Button is findable by
  -- its label text) and state their enabledness explicitly — Compose's
  -- `clickable` semantics, minus the onClick action closure (the MT test
  -- framework activates nodes through the real input pipeline instead).
  |>.semantics (mergeDescendants := true) (disabled := some !enabled)
  |>.focusable enabled
  |>.onFocusChanged (fun b =>
      match source with
      | some s => s.focused.set b
      | none => pure ())
  |>.onKeyEvent (fun ke =>
      if enabled && ke.isActivate then do onClick; pure true else pure false)
  |>.pointerInput key
    (if enabled then
      detectTapGestures
        (onTap := some fun _ => onClick)
        (onPress := some fun ps =>
          -- Cancellation mid-press (the `enabled`-flip relaunch, node
          -- removal) must not latch the flag — the flags-only analog of
          -- Compose's `PressInteraction.Cancel`.
          UiTask.onCancel (setPressed false) do
            setPressed true
            let _ ← ps.tryAwaitRelease
            setPressed false)
     else fun _ => pure ())

end Modifier

end Compose
