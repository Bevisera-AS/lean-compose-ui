import Compose.Runtime.Composer

namespace Compose

/-!
# Skippability support: `SkipEq` and changed-argument slots

The `composable` macro (see `Compose.Runtime.Macro`) skips a restartable
body when its scope is valid and every explicit argument is unchanged. Whether
"unchanged" is even decidable is a per-type, compile-time question: `SkipEq`
answers it with an instance-priority trick — types with `BEq` compare
structurally, all other types compare never-equal, silently disabling
skipping. This mirrors the Compose compiler plugin's stable/unstable parameter
classification feeding the `%changed` bits.

`Composer.changed` is the runtime half: one positional slot per explicit
argument in the restart group, storing the previous value and comparing the
next one against it. Mirrors `androidx.compose.runtime.Composer.changed`.
-/

/-- Compile-time-optional structural equality for the `composable` macro's
skip check: `eq a b = true` means the argument is certainly unchanged, so the
call may skip. Mirrors the stable/unstable parameter classification of the
Compose compiler plugin. -/
class SkipEq (α : Type) where
  /-- `true` iff the values are known-equal (skippable). -/
  eq : α → α → Bool

/-- Fallback for types without `BEq`: never equal, so such arguments simply
disable skipping (Compose's "unstable parameter" behavior). -/
instance (priority := low) : SkipEq α := ⟨fun _ _ => false⟩

/-- `BEq` types compare structurally, enabling skipping (Compose's "stable
parameter" behavior). -/
instance [BEq α] : SkipEq α := ⟨(· == ·)⟩

#guard SkipEq.eq (3 : Nat) 3                    -- BEq path: equal values skip
#guard !SkipEq.eq (3 : Nat) 4
#guard SkipEq.eq "label" "label"
#guard SkipEq.eq (some [1, 2]) (some [1, 2])
#guard !SkipEq.eq (id : Nat → Nat) id           -- no BEq: fallback never-equal
#guard !SkipEq.eq (fun (r : IO.Ref Nat) => r) (fun r => r)

namespace Composer

/-- Store-and-compare one restartable argument in the next positional slot of
the current (restart) group: on first composition the value is stored and the
argument counts as changed; afterwards the stored value is compared via
`SkipEq.eq` and replaced when it differs. The `composable` macro emits one
`changed` call per explicit parameter, in declaration order, before the skip
check. Mirrors `androidx.compose.runtime.Composer.changed`. -/
def changed (c : Composer) [SkipEq α] (a : α) : IO Bool := do
  have : Nonempty α := ⟨a⟩
  let fs ← c.frames.get
  let some f := fs.back?
    | throw <| IO.userError "Compose: changed outside an open group (composition misuse)"
  c.frames.set <| fs.set! (fs.size - 1) { f with slotCursor := f.slotCursor + 1 }
  if f.inserting then
    f.group.modifyData fun d => { d with slots := d.slots.push { val := SlotVal.mk a } }
    return true
  else
    let gd ← f.group.data
    if h : f.slotCursor < gd.slots.size then
      if SkipEq.eq (gd.slots[f.slotCursor].val.get! : α) a then
        return false
      else
        f.group.modifyData fun d =>
          { d with slots := d.slots.set! f.slotCursor { val := SlotVal.mk a } }
        return true
    else
      throw <| IO.userError
        "Compose: slot underflow — argument count changed within a restart group"

end Composer

end Compose
