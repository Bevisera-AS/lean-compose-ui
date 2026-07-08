import Sdl.Events

namespace Compose

/-!
# Key events (`Compose/Ui/Input/Keyboard.lean`)

The `KeyEvent` wrapper key handlers receive. Routing lives with the focus
system (`Compose.Ui.Input.Focus`): key events go to the focused node's
`Modifier.onKeyEvent` handlers first (innermost first), then its ancestors,
then app-level fallbacks (Tab traversal, Esc-clears-focus — installed by the
input router); `textInput` events go to the focused node's
`Modifier.onTextInput` handlers the same way.

**IME hook for M11**: `installInput` takes an `onTextClientFocused : Bool →
IO Unit` callback, invoked whenever focus lands on / leaves a node whose
chain has an `onTextInput` handler (a *text-input client*). M11's TextField
wires it to `Window.startTextInput`/`stopTextInput` (+ `setTextInputArea`
from its caret rect); M6 defaults it to a no-op. `textEditing` (composition)
events route to the focused node's `Modifier.onTextEditing` (M11).
-/

/-- One keyboard key press/release, as routed to `Modifier.onKeyEvent`.
Mirrors `androidx.compose.ui.input.key.KeyEvent` (with SDL's keycode/scancode
split instead of Android key codes). -/
structure KeyEvent where
  /-- Layout-mapped key. -/
  key : Sdl.Keycode
  /-- Physical key position. -/
  scancode : Sdl.Scancode := .unknown
  /-- Modifiers held at event time. -/
  mods : Sdl.Keymod := .none
  /-- `true` = key down, `false` = key up. -/
  down : Bool := true
  /-- OS auto-repeat (down only). -/
  isRepeat : Bool := false
  /-- SDL timestamp, nanoseconds. -/
  timestamp : UInt64 := 0
  deriving Repr, Inhabited

namespace KeyEvent

/-- Wrap an SDL keyboard event (`keyDown`/`keyUp` payload). -/
def ofSdl (e : Sdl.KeyboardEvent) : KeyEvent :=
  { key := e.key, scancode := e.scancode, mods := e.mod
    down := e.down, isRepeat := e.repeat, timestamp := e.timestamp }

/-- Whether any Shift is held. -/
def hasShift (e : KeyEvent) : Bool := (e.mods &&& .shift) != .none

/-- Whether this is a keyboard *activation* press (Enter or Space, down,
not a repeat) — what `Modifier.clickable` treats as a click. Mirrors
`Key.Enter`/`Key.Spacebar` handling in Compose's `Modifier.clickable`. -/
def isActivate (e : KeyEvent) : Bool :=
  e.down && !e.isRepeat && (e.key == .return || e.key == .space || e.key == .kpEnter)

#guard ({ key := .space } : KeyEvent).isActivate
#guard ({ key := .return } : KeyEvent).isActivate
#guard !({ key := .return, down := false } : KeyEvent).isActivate
#guard !({ key := .return, isRepeat := true } : KeyEvent).isActivate
#guard !({ key := .a } : KeyEvent).isActivate
#guard ({ key := .tab, mods := .lShift } : KeyEvent).hasShift
#guard !({ key := .tab } : KeyEvent).hasShift

end KeyEvent

end Compose
