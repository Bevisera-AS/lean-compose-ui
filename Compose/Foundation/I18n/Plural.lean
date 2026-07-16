module

public section

namespace Compose.I18n

/-!
# Plural rules

CLDR cardinal plural categories for integer counts, as pure per-language
functions. Only the categories integers can reach are modeled (CLDR's
fraction-driven cases — Czech `many`, Portuguese `many` for compact
millions — need decimal operands and cannot fire for `Int` counts; UI
counts are integers).

App usage: a strings-record field is a function of the count —
`sessions := fun n => plural (rule n) "1 session" (other := s!"{n} sessions")`.
-/

/-- A CLDR cardinal category (the subset reachable from integers in the
shipped rules). -/
inductive PluralCategory where
  | one
  | few
  | other
  deriving BEq, Repr, Inhabited

/-- A language's cardinal rule for integer counts. -/
abbrev PluralRule := Int → PluralCategory

namespace PluralRule

/-- English (also German, Dutch, Italian…): `one` iff exactly 1. CLDR:
`i = 1 and v = 0`. -/
def en : PluralRule := fun n => if n == 1 then .one else .other

#guard en 1 == .one
#guard en 0 == .other
#guard en 2 == .other
#guard en (-1) == .other  -- CLDR operates on |n|=1… `n = 1` only

/-- Czech: `one` = 1, `few` = 2–4, `other` otherwise (CLDR `i = 1`,
`i = 2..4 and v = 0`; the fraction-only `many` is unreachable for ints). -/
def cs : PluralRule := fun n =>
  if n == 1 then .one
  else if 2 ≤ n && n ≤ 4 then .few
  else .other

#guard cs 1 == .one
#guard cs 2 == .few
#guard cs 3 == .few
#guard cs 4 == .few
#guard cs 5 == .other
#guard cs 0 == .other
#guard cs 100 == .other

/-- Portuguese: `one` = 0 or 1 (CLDR `i = 0..1`; the compact-million `many`
is unreachable for plain counts). -/
def pt : PluralRule := fun n =>
  if 0 ≤ n && n ≤ 1 then .one else .other

#guard pt 0 == .one
#guard pt 1 == .one
#guard pt 2 == .other

/-- Vietnamese (also Japanese, Korean, Thai…): no plural distinction. -/
def vi : PluralRule := fun _ => .other

#guard vi 0 == .other
#guard vi 1 == .other
#guard vi 7 == .other

/-- CLDR root rule: `other` only — the honest fallback for languages the
table doesn't know. -/
def root : PluralRule := vi

end PluralRule

/-- Select a form by category, with `other` as the required fallback (a
category the language never produces just falls through). Mirrors how
`plurals` resources resolve. -/
def plural (c : PluralCategory) (other : String)
    (one : Option String := none) (few : Option String := none) : String :=
  match c with
  | .one => one.getD other
  | .few => few.getD (one.getD other)
  | .other => other

#guard plural (PluralRule.cs 2) "sezení" (one := some "sezení")
  (few := some "sezení (few)") == "sezení (few)"
#guard plural (PluralRule.en 5) "sessions" (one := some "session") == "sessions"
#guard plural (PluralRule.vi 1) "phiên" == "phiên"

end Compose.I18n

end
