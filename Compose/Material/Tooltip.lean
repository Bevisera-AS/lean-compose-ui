import Compose.Material.Surface
import Compose.Material.Text
import Compose.Material.StateLayer
import Compose.Ui.Overlay

namespace Compose

/-!
# Tooltip (`Compose/Material/Tooltip.lean`)

`TooltipArea`, mirroring Compose Desktop's
`androidx.compose.foundation.TooltipArea` on the M10 overlay stack:

* The pointer entering `content` arms a **scheduler timer** (`delayMs`); when
  it elapses the tooltip shows in a `Popup` anchored a little below-right of
  the cursor (`resolvePopupPosition` clamps it into the window).
* Any pointer exit or press hides it immediately and cancels a pending timer
  (a `UiTask.race` between the delay and the next exit/press — whichever wins
  decides visibility). Re-entering arms a fresh delay.
* The tooltip container is a non-dismissable, non-focusable popup, so it never
  steals key routing; its `Surface` carries no pointer handlers, and it is
  offset off the cursor so the pointer does not wander onto it and flicker.

`Tooltip` is the convenience for the common label case: a small themed
surface around a line of text.
-/

/-- Await pointer events on `scope` until one ends the hover: an `exit`
(pointer left the content) or a `press`. Moves pass through. -/
private partial def awaitTooltipEnd (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .exit | .press => pure ()
  | _ => awaitTooltipEnd scope

/-- The `TooltipArea` pointer coroutine: on `enter`, record the cursor in
window coordinates (content rect origin + local position) and race the delay
against the next exit/press — the delay winning shows the tooltip, an
exit/press hiding it. `exit`/`press` outside a race hide it too. -/
private partial def tooltipGesture (rectRef : IO.Ref Rect) (pos : MutableState Offset)
    (visible : MutableState Bool) (delayRef : IO.Ref Nat)
    (scope : PointerInputScope) : UiTask Unit := do
  let ev ← scope.awaitEvent
  match ev.eventType with
  | .enter =>
    let r ← rectRef.get
    pos.set ⟨r.left + ev.position.x, r.top + ev.position.y⟩
    let ms ← delayRef.get
    let shown ← UiTask.race
      (do UiTask.delay ms.toUInt32; pure true)
      (do awaitTooltipEnd scope; pure false)
    visible.set shown
  | .exit | .press => visible.set false
  | _ => pure ()
  tooltipGesture rectRef pos visible delayRef scope

/-- Show `tooltip` in a popup while the pointer rests over `content` for at
least `delayMs`; exit or press hides it. Mirrors Compose Desktop's
`androidx.compose.foundation.TooltipArea` (see the module docstring for the
overlay/positioning details). Use `Tooltip` for the common text case. -/
composable def TooltipArea (tooltip : Composable Unit) (content : Composable Unit)
    (delayMs : Nat := 500) (modifier : Modifier := {}) : Composable Unit := do
  let visible ← remember (mutableStateOf false)
  let pos ← remember (mutableStateOf Offset.zero)
  let rectRef ← remember (IO.mkRef Rect.zero)
  let delayRef ← rememberUpdatedRef delayMs
  let id ← remember freshId
  let m := modifier.onGloballyPositioned rectRef.set
    |>.pointerInput (mixKeys (stringKey "Compose.TooltipArea") id.toUInt64)
        (tooltipGesture rectRef pos visible delayRef)
  Box content (modifier := m)
  if ← visible.get then
    let p ← pos.get
    Popup tooltip (anchor := some ⟨p.x, p.y, p.x, p.y⟩) (offset := ⟨8, 20⟩)

/-- A small themed surface around a line of text — the default tooltip body,
Material's compact `PlainTooltip` look (`surfaceVariant` container, small
shape, tight padding, body typography). -/
composable def TooltipSurface (text : String) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let shapes ← MaterialTheme.shapes
  let typo ← MaterialTheme.typography
  Surface (modifier := Modifier.padding (horizontal := some 8) (vertical := some 4))
      (shape := shapes.extraSmall) (color := some colors.surfaceVariant)
      (border := some { width := 1, color := colors.outlineVariant }) do
    Text text (style := typo.bodyMedium)

/-- `TooltipArea` with the default `TooltipSurface` body — the common
"hover a control, see a text label" case. -/
composable def Tooltip (text : String) (content : Composable Unit)
    (delayMs : Nat := 500) (modifier : Modifier := {}) : Composable Unit :=
  TooltipArea (TooltipSurface text) content (delayMs := delayMs)
    (modifier := modifier)

end Compose
