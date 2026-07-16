module

public import Compose.Runtime.SlotVal
public meta import Compose.Runtime.SlotVal

public section

namespace Compose

/-!
# Applier

The runtime edits the emitted-node tree exclusively through this abstraction,
mirroring `androidx.compose.runtime.Applier`. The UI layer instantiates
`N := LayoutNode`; runtime tests instantiate a labeled test tree. The composer
itself works over the erased `NodeApplier` so `GroupData` needs no type
parameter.
-/

/-- Tree mutator for emitted nodes. All indices are positions in the parent's
child list. Mirrors `androidx.compose.runtime.Applier` (bottom-up insertion is
not modeled; insertion is immediate, top-down). -/
structure Applier (N : Type) where
  /-- The root node every composition attaches to. Mirrors `Applier.root`. -/
  root : N
  /-- Insert `child` at `index` in `parent`. Mirrors `insertTopDown`. -/
  insert : (parent : N) → (index : Nat) → (child : N) → IO Unit
  /-- Remove `count` children starting at `index`. Mirrors `Applier.remove`. -/
  remove : (parent : N) → (index : Nat) → (count : Nat) → IO Unit
  /-- Move `count` children from `fromIndex` to `toIndex` (both indices in the
  pre-move list, Compose convention). Mirrors `Applier.move`. -/
  move : (parent : N) → (fromIndex : Nat) → (toIndex : Nat) → (count : Nat) → IO Unit
  /-- Called when the composition is disposed. Mirrors `Applier.clear`. -/
  onClear : IO Unit := pure ()

/-- An applier with the node type erased to `NodeVal`; what `Composer` drives. -/
abbrev NodeApplier := Applier NodeVal

/-- Erase a typed applier to a `NodeApplier`. Every `NodeVal` handed to the
erased applier was produced by `NodeVal.mk` at type `N`, so the unboxing is
sound (see `Compose.Runtime.SlotVal`). This is the typed construction helper
for compositions: build an `Applier N`, erase it, compose over it. -/
def Applier.erase [Nonempty N] (a : Applier N) : NodeApplier where
  root := .mk a.root
  insert p i ch := a.insert p.get! i ch.get!
  remove p i n := a.remove p.get! i n
  move p f t n := a.move p.get! f t n
  onClear := a.onClear

end Compose

end
