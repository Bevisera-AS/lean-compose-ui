module

public import Compose.Ui.Window
public meta import Compose.Ui.Window

public section

/-!
# BackHandler

Interception of the platform back action (the `AC_BACK` key — Android's
back button/gesture when the embedder traps it; any platform can synthesize
it). Handlers ride the window's overlay key-handler chain, so they compose
with `Popup`/`Dialog` for free: the innermost (last-registered) party gets
the first look — an open dialog dismisses, then the deepest enabled
`BackHandler` fires, and an event nobody consumes reaches the shell, which
quits the loop (on Android the activity then finishes — exactly the
default back behavior).

Everything acts on key-*down* (non-repeat), one consumer per press.
Desktop note: Esc keeps its focus/dismiss meanings and is *not* a back
alias; tests drive back with a synthesized `AC_BACK` key.
-/

namespace Compose

/-- Run `onBack` when the platform back action fires while this composable
is in the composition and `enabled`. Nesting: the innermost enabled handler
wins. Mirrors `androidx.activity.compose.BackHandler` (same
last-registered-wins dispatch). -/
composable def BackHandler (onBack : IO Unit) (enabled : Bool := true) :
    Composable Unit := do
  match ← LocalWindowContext.current with
  | none => pure () -- windowless composition (pure headless): nothing to hook
  | some ctx =>
    let id ← remember freshId
    let enabledRef ← rememberUpdatedRef enabled
    let backRef ← rememberUpdatedRef onBack
    DisposableEffect id do
      ctx.registerKeyHandler
        { id
          capture := false
          handler := fun ke => do
            if ke.down && !ke.isRepeat && ke.key == .acBack then
              if ← enabledRef.get then
                (← backRef.get)
                return true
            return false }
      return (ctx.unregisterKeyHandler id)

end Compose

end
