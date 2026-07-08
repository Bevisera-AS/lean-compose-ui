import Compose.Runtime.Composer
import Compose.Runtime.State

namespace Compose

/-!
# CompositionLocal

Ambient, tree-scoped values. Two flavors, mirroring Compose:

- **dynamic** (`compositionLocalOf`): the provider stores a `MutableState`
  cell in the provided-values map, so `.current` reads register with the
  ambient observer like any state read, and a provider value change
  invalidates exactly the readers.
- **static** (`staticCompositionLocalOf`): the raw value is stored; reads are
  free (no registration) but a provider value change invalidates every
  restart scope in the provider's subtree.

Provided values are carried on the composer in a persistent `LocalMap`; each
restart scope captures the map in effect at its position so standalone
re-runs resolve the same values.
-/

/-- An ambient value keyed by identity, resolved through the nearest
enclosing provider. Mirrors `androidx.compose.runtime.CompositionLocal`. -/
structure CompositionLocal (α : Type) where
  id : Nat
  /-- Value seen without an enclosing provider. -/
  defaultValue : α
  /-- Static locals recompose the provider subtree on change instead of
  tracking readers. -/
  isStatic : Bool
  /-- Change detection for provided values. -/
  eq : α → α → Bool

instance [Nonempty α] : Nonempty (CompositionLocal α) :=
  ⟨{ id := 0, defaultValue := Classical.choice inferInstance,
     isStatic := false, eq := fun _ _ => true }⟩

/-- Create a dynamic `CompositionLocal`: reads register like state reads and
only readers recompose when a provider's value changes. Mirrors
`androidx.compose.runtime.compositionLocalOf` (structural equality policy). -/
def compositionLocalOf [BEq α] (default : α) : IO (CompositionLocal α) :=
  return { id := ← freshId, defaultValue := default, isStatic := false, eq := (· == ·) }

/-- Create a static `CompositionLocal`: reads are unregistered (cheap), and a
provider value change recomposes the whole provider subtree. Mirrors
`androidx.compose.runtime.staticCompositionLocalOf`. -/
def staticCompositionLocalOf [BEq α] (default : α) : IO (CompositionLocal α) :=
  return { id := ← freshId, defaultValue := default, isStatic := true, eq := (· == ·) }

/-- Invalidate every restart scope in `g`'s subtree (static provider change). -/
private partial def invalidateSubtreeScopes (g : Group) : IO Unit := do
  let gd ← g.data
  if let some s := gd.scope then
    s.invalidate
  gd.children.forM invalidateSubtreeScopes

/-- Provide `value` for `l` while composing `content`. Mirrors
`androidx.compose.runtime.CompositionLocalProvider` (single binding). -/
def CompositionLocalProvider (l : CompositionLocal α) (value : α)
    (content : Composable Unit) : Composable Unit := fun c => do
  have : Nonempty α := ⟨value⟩
  let g ← c.startGroup (mixKeys providerGroupSalt l.id.toUInt64) (isNode := false)
  let saved ← c.locals.get
  let entry ←
    if l.isStatic then do
      -- Track the previously provided value; on change, recompose the subtree.
      let prev ← c.remember (IO.mkRef value)
      unless l.eq (← prev.get) value do
        prev.set value
        invalidateSubtreeScopes g
      pure (SlotVal.mk value)
    else do
      -- The cell's identity is stable across recompositions; only its value
      -- changes, invalidating exactly the registered readers.
      let cell ← c.remember (mutableStateOfPolicy l.eq value)
      cell.set value
      pure (SlotVal.mk cell)
  c.locals.set (saved.insert l.id entry)
  content.run c
  c.locals.set saved
  c.endGroup

/-- Read the current value for this local: the innermost provided value, or
the default. Dynamic locals register the read with the ambient observer.
Mirrors `CompositionLocal.current`. -/
def CompositionLocal.current (l : CompositionLocal α) : Composable α := fun c => do
  have : Nonempty α := ⟨l.defaultValue⟩
  match (← c.locals.get).find? l.id with
  | none => return l.defaultValue
  | some sv =>
    if l.isStatic then
      return sv.get!
    else
      (sv.get! : MutableState α).get

end Compose
