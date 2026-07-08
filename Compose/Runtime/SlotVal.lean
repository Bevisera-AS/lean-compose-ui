namespace Compose

/-!
# Heterogeneous slot storage

Positional memoization stores values of arbitrary types in a group's slot
array, mirroring the untyped `Any?` slots of
`androidx.compose.runtime.SlotTable`. `SlotVal` is a dynamic box built on
`unsafeCast` behind a safe `opaque` interface (`@[implemented_by]` bridges to
the unsafe implementations).

**Soundness invariant** (audited, relied on by the whole runtime): a `SlotVal`
is only ever read back with `get!` at the *same static type* it was created
with by `mk`. The composer guarantees this positionally: a slot is only read
back at the same group key and slot index where it was written, so the type at
the read site equals the type at the write site. The two other uses keep the
invariant trivially: `NodeVal` boxes are written and read at the applier's
single node type, and `Group` boxes (see `Compose.Runtime.Composer`) always
hold an `IO.Ref GroupData`.

This is the **only** module in the codebase allowed to use `unsafeCast`.
-/

private opaque SlotValPointed : NonemptyType

/-- A type-erased slot value. Mirrors the untyped slots of
`androidx.compose.runtime.SlotTable`. See the module docstring for the
soundness invariant governing `mk`/`get!`. -/
def SlotVal : Type := SlotValPointed.type

instance : Nonempty SlotVal := SlotValPointed.property

namespace SlotVal

private unsafe def mkImpl {α : Type} (a : α) : SlotVal := unsafeCast a

/-- Box a value of any type into a `SlotVal`. -/
@[implemented_by mkImpl]
opaque mk {α : Type} (a : α) : SlotVal

private unsafe def getImpl {α : Type} [Nonempty α] (v : SlotVal) : α := unsafeCast v

/-- Unbox a `SlotVal`. Sound only when `α` is the exact type the box was
created with (see the module docstring); anything else is undefined behavior,
which the composer's positional discipline rules out. -/
@[implemented_by getImpl]
opaque get! {α : Type} [Nonempty α] (v : SlotVal) : α

#guard (mk (42 : Nat) |>.get! : Nat) == 42
#guard (mk "slot" |>.get! : String) == "slot"
#guard (mk (some [1, 2] : Option (List Nat)) |>.get! : Option (List Nat)) == some [1, 2]

end SlotVal

/-- Panic/default value only (a boxed `Unit`), so containers of slots can use
`!`-indexing; it must never be read back at another type. -/
instance : Inhabited SlotVal := ⟨SlotVal.mk ()⟩

/-- A type-erased applier node: what the runtime threads through
`emitNode`/`Applier` so `Compose.Runtime` stays independent of the concrete
node type (`LayoutNode` in the UI layer, a test node in the test suite).
Mirrors the erased `N` of `androidx.compose.runtime.Applier`. -/
def NodeVal : Type := SlotVal

instance : Nonempty NodeVal := inferInstanceAs (Nonempty SlotVal)

namespace NodeVal

/-- Box a node. The same soundness invariant as `SlotVal.mk` applies: one
composition uses a single concrete node type throughout. -/
def mk {α : Type} (a : α) : NodeVal := SlotVal.mk a

/-- Unbox a node at the applier's concrete node type. -/
def get! {α : Type} [Nonempty α] (n : NodeVal) : α := SlotVal.get! n

#guard (mk (7 : Nat) |>.get! : Nat) == 7

end NodeVal

end Compose
