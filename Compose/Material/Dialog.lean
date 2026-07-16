module

public import Compose.Material.Surface
public meta import Compose.Material.Surface
public import Compose.Material.Text
public meta import Compose.Material.Text
public import Compose.Ui.Overlay
public meta import Compose.Ui.Overlay

public section

namespace Compose

/-!
# AlertDialog (`Compose/Material/Dialog.lean`)

The Material alert dialog over the `Ui` overlay `Dialog`: a centered
`shapes.large` Surface with title (`titleLarge`), body text
(`bodyMedium`/`onSurfaceVariant`), and end-aligned action buttons; the scrim
swallows all input below, Esc/scrim-click call `onDismissRequest`. Mirrors
`androidx.compose.material3.AlertDialog` (string title/text M10 shape —
no icon slot, no shadows).
-/

/-- A Material alert dialog (see the module docstring). `confirmButton`
(and the optional `dismissButton`, placed before it) are composables —
typically `TextButton`s whose `onClick` closes the dialog. Mirrors
`androidx.compose.material3.AlertDialog`. -/
composable def AlertDialog (onDismissRequest : IO Unit) (title : String)
    (text : String) (confirmButton : Composable Unit)
    (dismissButton : Option (Composable Unit) := none)
    (modifier : Modifier := {}) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let typo ← MaterialTheme.typography
  let shapes ← MaterialTheme.shapes
  Dialog onDismissRequest do
    Surface (modifier := modifier.semantics (role := some .dialog)
        |>.sizeIn (minWidth := some 280) (maxWidth := some 560))
      (shape := shapes.large) (color := some colors.surface) (elevation := 6) do
      Column (modifier := Modifier.padding (all := 24))
          (verticalArrangement := .spacedBy 16) do
        Text title (style := typo.titleLarge)
        Text text (style := typo.bodyMedium) (color := some colors.onSurfaceVariant)
        Row (modifier := Modifier.fillMaxWidth) (horizontalArrangement := .«end»)
            (verticalAlignment := .centerVertically) do
          match dismissButton with
          | some b => do b; Spacer (Modifier.width 8)
          | none => pure ()
          confirmButton

end Compose

end
