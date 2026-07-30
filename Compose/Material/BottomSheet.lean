module

public import Compose.Material.Surface
public meta import Compose.Material.Surface
public import Compose.Ui.Overlay
public meta import Compose.Ui.Overlay
public import Compose.Animation.Visibility
public meta import Compose.Animation.Visibility
public import Compose.Foundation.Gestures
public meta import Compose.Foundation.Gestures

public section

namespace Compose

/-!
# ModalBottomSheet

A modal sheet anchored to the bottom edge: scrim (tap dismisses), slide-in
enter, drag-down dismissal past a threshold, and — riding the shared
overlay chassis — Esc/back dismissal and modal focus scoping for free.

Documented simplifications vs. `androidx.compose.material3.ModalBottomSheet`:
one expanded state (no half-expand), no nested-scroll handoff from inner
scrollables, a fixed drag-dismiss threshold instead of velocity settling,
and dismissal unmounts immediately (the enter edge animates; the exit is
the app flipping its `show` state).
-/

/-- Drag distance (dp) past which releasing dismisses the sheet. -/
def sheetDismissThreshold : Dp := 96

/-- The pill-shaped drag handle. -/
composable def sheetHandle : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Box (modifier := Modifier.fillMaxWidth.padding (vertical := some 12))
      (contentAlignment := .center) do
    Layout (Modifier.size 32 4
      |>.background (colors.onSurfaceVariant.withAlpha 0.4) (.roundedCorners 2 2 2 2))
      .leaf

/-- A modal bottom sheet. Compose it while your `show` state is true;
`onDismissRequest` fires on scrim tap, Esc/back, and drag-down release. -/
composable def ModalBottomSheet (onDismissRequest : IO Unit)
    (content : Composable Unit := pure ()) (modifier : Modifier := {})
    (blurBehind : Dp := 0) : Composable Unit := do
  let density ← LocalDensity.current
  -- The themed scrim (`MaterialTheme` provides it as `colors.scrim` at
  -- `tokens.scrimAlpha`), like `Dialog` — not a hardcoded black.
  let scrim ← LocalScrimColor.current
  let dismissRef ← rememberUpdatedRef onDismissRequest
  -- Downward drag displacement, px. A plain state: dragging writes it every
  -- move; release either dismisses or snaps back.
  let drag ← remember (mutableStateOf (0.0 : Float32))
  -- Enter: mount hidden, flip shown → the slide-in plays.
  let shown ← remember (mutableStateOf false)
  LaunchedEffect () (shown.set true)
  overlayImpl (anchor := none) (alignment := .bottomCenter) (offset := ⟨0, 0⟩)
    (onDismissRequest := some (do (← dismissRef.get)))
    (focusable := true) (onKeyEvent := fun _ => pure false)
    (scrimColor := some scrim) (modal := true) (interactive := true)
    (blurBehind := blurBehind) do
    let colors ← MaterialTheme.colorScheme
    let tokens ← MaterialTheme.tokens
    let dragPx ← drag.get
    AnimatedVisibility (← shown.get)
      (enter := slideInVertically (initialOffsetY := 1.0))
      (exit := slideOutVertically (targetOffsetY := 1.0))
      (content := do
        Surface (modifier := modifier.fillMaxWidth
            |>.offset 0 (density.pxToDp dragPx)
            |>.pointerInput (stringKey "Compose.Material.BottomSheet.drag")
              (detectDragGestures
                (onDrag := fun _ d => drag.modify fun v => max 0 (v + d.y))
                (onDragEnd := do
                  if (← drag.get) > density.dpToPx sheetDismissThreshold then
                    (← dismissRef.get)
                  else
                    drag.set 0)
                (onDragCancel := drag.set 0)))
          (shape := .roundedCorners 28 28 0 0)
          (color := some colors.surfaceContainerLow)
          (material := some tokens.materials.chrome) do
          Column (modifier := Modifier.fillMaxWidth) do
            sheetHandle
            content)

end Compose

end
