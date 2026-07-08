namespace Compose

/-!
# Text editing model (`Compose/Ui/Text/EditModel.lean`)

The **pure** editing model behind M11's `TextField` (DESIGN.md): a
`TextFieldValue {text, selection, composition}` transformed by `EditCommand`s
through `TextFieldValue.apply` — no `IO`, no SDL, exhaustively `#guard`-tested
right here. Mirrors `androidx.compose.ui.text.input.TextFieldValue` +
`EditCommand`/`EditProcessor`.

All offsets are **UTF-8 byte offsets** into `text` (SDL_ttf's native unit —
see `TextLayout.hitToByteOffset`), always kept on codepoint boundaries: every
command snaps incoming offsets and navigates via boundary-safe helpers
(`Utf8.*`), so a codepoint is never split.

Documented simplifications:
* **Word boundaries**: a *word char* is an ASCII alphanumeric or any
  non-ASCII codepoint (so `héllo`/`日本語` are single words); everything else
  separates. Word motions skip separators first, then the word run —
  `wordLeft` lands at the start of the previous word, `wordRight` just past
  the end of the next one (both "eat" intervening spaces).
* **Single line**: `home`/`end` mean start/end of the whole string (the
  TextField is single-line by design).
* Any command other than `setComposition`/`commitComposition`/`insert`
  implicitly *finishes* an active composition (text kept, marker cleared)
  before applying — the platform-typical "moving the caret commits the IME".
  `insert` and `setComposition` instead *replace* the composition region.
-/

namespace Utf8

/-! UTF-8 boundary-safe navigation over byte offsets. The walk-based helpers
are O(n) in the string length — fine for single-line text-field content. -/

/-- The largest codepoint boundary ≤ `off` (clamped to the string size). -/
def floor (s : String) (off : Nat) : Nat := Id.run do
  let n := s.utf8ByteSize
  if off ≥ n then return n
  let mut p : String.Pos.Raw := ⟨0⟩
  for _ in [0:s.length] do
    let q := p.next s
    if q.byteIdx > off then return p.byteIdx
    p := q
  return p.byteIdx

/-- Whether `off` sits on a codepoint boundary (or at either end). -/
def isBoundary (s : String) (off : Nat) : Bool :=
  floor s off == off

/-- The boundary after `off` (snapping `off` down first); the size at the end. -/
def next (s : String) (off : Nat) : Nat :=
  let p := floor s off
  if p ≥ s.utf8ByteSize then p
  else (String.Pos.Raw.next s ⟨p⟩).byteIdx

/-- The boundary before `off` (snapping `off` down first); `0` at the start.
When `off` is mid-codepoint this is the enclosing codepoint's start. -/
def prev (s : String) (off : Nat) : Nat :=
  let p := floor s off
  if isBoundary s off then
    if p == 0 then 0 else (String.Pos.Raw.prev s ⟨p⟩).byteIdx
  else p

/-- The codepoint starting at boundary `off` (undefined-ish past the end —
callers bound-check). -/
def charAt (s : String) (off : Nat) : Char :=
  String.Pos.Raw.get s ⟨off⟩

/-- Word-char classification (see the module docstring): ASCII alphanumerics
and all non-ASCII codepoints are word constituents. -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c.val ≥ 0x80

/-- Start of the word run left of `off`: skip separators leftward, then the
word run. Mirrors the caret motion of ctrl/option-Left. -/
def wordLeft (s : String) (off : Nat) : Nat := Id.run do
  let mut p := floor s off
  -- Skip separators.
  for _ in [0:s.length] do
    if p == 0 then return 0
    if isWordChar (charAt s (prev s p)) then break
    p := prev s p
  -- Skip the word run.
  for _ in [0:s.length] do
    if p == 0 then return 0
    if !isWordChar (charAt s (prev s p)) then return p
    p := prev s p
  return p

/-- Just past the word run right of `off`: skip separators rightward, then
the word run. Mirrors the caret motion of ctrl/option-Right. -/
def wordRight (s : String) (off : Nat) : Nat := Id.run do
  let n := s.utf8ByteSize
  let mut p := floor s off
  for _ in [0:s.length] do
    if p ≥ n then return n
    if isWordChar (charAt s p) then break
    p := next s p
  for _ in [0:s.length] do
    if p ≥ n then return n
    if !isWordChar (charAt s p) then return p
    p := next s p
  return p

/-- The word run containing `off` as `(start, end)` byte offsets (used by
double-click selection): a word char expands over its run; a separator
selects just itself; an empty string gives `(0, 0)`. -/
def wordRangeAt (s : String) (off : Nat) : Nat × Nat := Id.run do
  let n := s.utf8ByteSize
  if n == 0 then return (0, 0)
  let mut p := floor s off
  if p ≥ n then p := prev s n
  if !isWordChar (charAt s p) then return (p, next s p)
  let mut a := p
  for _ in [0:s.length] do
    if a == 0 then break
    if !isWordChar (charAt s (prev s a)) then break
    a := prev s a
  let mut b := next s p
  for _ in [0:s.length] do
    if b ≥ n then break
    if !isWordChar (charAt s b) then break
    b := next s b
  return (a, b)

/-- Byte offset of the `cp`-th codepoint (clamped to the string size) —
converts SDL's codepoint-indexed IME cursor into our byte offsets. -/
def codepointToByte (s : String) (cp : Nat) : Nat := Id.run do
  let mut p : Nat := 0
  let mut i : Nat := 0
  for _ in [0:s.length] do
    if i ≥ cp then return p
    p := next s p
    i := i + 1
  return p

-- boundary math on "héllo" (h=1, é=2, l=1, l=1, o=1 bytes → boundaries 0,1,3,4,5,6)
#guard floor "héllo" 2 == 1
#guard floor "héllo" 3 == 3
#guard floor "héllo" 99 == 6
#guard isBoundary "héllo" 1 && isBoundary "héllo" 3 && !isBoundary "héllo" 2
#guard next "héllo" 1 == 3
#guard next "héllo" 6 == 6
#guard prev "héllo" 3 == 1
#guard prev "héllo" 2 == 1   -- mid-codepoint snaps to its start
#guard prev "héllo" 0 == 0
-- 3-byte and 4-byte codepoints
#guard next "日本語" 0 == 3 && next "日本語" 3 == 6
#guard prev "日本語" 9 == 6
#guard next "a😀b" 1 == 5 && prev "a😀b" 5 == 1
#guard floor "" 3 == 0 && next "" 0 == 0 && prev "" 0 == 0
-- word classification and motions
#guard isWordChar 'a' && isWordChar '7' && isWordChar 'é' && isWordChar '日'
#guard !isWordChar ' ' && !isWordChar '-' && !isWordChar '.'
#guard wordRight "foo bar  baz" 0 == 3
#guard wordRight "foo bar  baz" 3 == 7    -- eats the space, stops after "bar"
#guard wordRight "foo bar  baz" 7 == 12
#guard wordRight "foo" 3 == 3
#guard wordLeft "foo bar  baz" 12 == 9
#guard wordLeft "foo bar  baz" 9 == 4     -- eats both spaces, lands at "bar"
#guard wordLeft "foo bar  baz" 4 == 0
#guard wordLeft "  foo" 2 == 0
#guard wordLeft "" 0 == 0 && wordRight "" 0 == 0
#guard wordLeft "héllo x" 8 == 7 && wordLeft "héllo x" 7 == 0
#guard wordRight "日本語 ok" 0 == 9
-- word range (double-click)
#guard wordRangeAt "foo bar" 5 == (4, 7)
#guard wordRangeAt "foo bar" 0 == (0, 3)
#guard wordRangeAt "foo bar" 3 == (3, 4)  -- separator selects itself
#guard wordRangeAt "foo bar" 7 == (4, 7)  -- end of string: word before
#guard wordRangeAt "héllo" 4 == (0, 6)
#guard wordRangeAt "" 0 == (0, 0)
-- codepoint → byte
#guard codepointToByte "héllo" 0 == 0
#guard codepointToByte "héllo" 1 == 1
#guard codepointToByte "héllo" 2 == 3
#guard codepointToByte "日本語" 2 == 6
#guard codepointToByte "abc" 99 == 3

end Utf8

/-- A selection/composition range as UTF-8 byte offsets, stored as
`anchor` (where the selection started) and `active` (the moving end — the
caret). `start`/`end` are the normalized accessors (`start ≤ end`); a
collapsed range (`anchor == active`) is a caret. Mirrors
`androidx.compose.ui.text.TextRange` (which also keeps direction). -/
structure TextRange where
  /-- The fixed end (where a shift-extension or drag started). -/
  anchor : Nat := 0
  /-- The moving end — where the caret is drawn. -/
  active : Nat := 0
  deriving Repr, BEq, Inhabited

namespace TextRange

/-- A collapsed range (caret) at `off`. Mirrors `TextRange(off)`. -/
def caret (off : Nat) : TextRange := ⟨off, off⟩

/-- The smaller offset. Mirrors `TextRange.min`. -/
def start (r : TextRange) : Nat := min r.anchor r.active

/-- The larger offset. Mirrors `TextRange.max`. -/
def «end» (r : TextRange) : Nat := max r.anchor r.active

/-- Whether the range is a caret. Mirrors `TextRange.collapsed`. -/
def collapsed (r : TextRange) : Bool := r.anchor == r.active

/-- Byte length of the covered span. Mirrors `TextRange.length`. -/
def length (r : TextRange) : Nat := r.«end» - r.start

#guard (caret 5).collapsed && (caret 5).start == 5 && (caret 5).«end» == 5
#guard (⟨7, 2⟩ : TextRange).start == 2 && (⟨7, 2⟩ : TextRange).«end» == 7
#guard (⟨7, 2⟩ : TextRange).length == 5 && !(⟨7, 2⟩ : TextRange).collapsed

end TextRange

/-- The full editable state of a text field: the text, the selection/caret,
and the IME composition region (the span being composed, drawn underlined),
if any. Mirrors `androidx.compose.ui.text.input.TextFieldValue`. -/
structure TextFieldValue where
  text : String := ""
  selection : TextRange := {}
  composition : Option TextRange := none
  deriving Repr, BEq, Inhabited

/-- One editing operation on a `TextFieldValue` — see `TextFieldValue.apply`.
Mirrors `androidx.compose.ui.text.input.EditCommand` (union of the commit/
set/delete/move commands, plus explicit caret motions Compose leaves to the
platform text toolkit). -/
inductive EditCommand where
  /-- Replace the selection (or the composition region, if composing) with
  `text`; caret lands after it. Mirrors `CommitTextCommand`. -/
  | insert (text : String)
  /-- Delete the selection, or the codepoint before a collapsed caret. -/
  | backspace
  /-- Delete the selection, or the codepoint after a collapsed caret. -/
  | deleteForward
  /-- Delete the selection, or back to `Utf8.wordLeft` of the caret. -/
  | deleteWordBack
  /-- Delete the selection, or forward to `Utf8.wordRight` of the caret. -/
  | deleteWordForward
  /-- Delete the selection (no-op when collapsed). -/
  | deleteSelection
  /-- Caret left one codepoint; a non-extended motion over a selection
  collapses to its start without moving. `extend` moves `active` only. -/
  | left (extend : Bool := false)
  /-- Caret right one codepoint (collapses to the selection end). -/
  | right (extend : Bool := false)
  /-- Caret to the start of the previous word (from the selection's left
  edge when not extending). -/
  | wordLeft (extend : Bool := false)
  /-- Caret past the end of the next word (from the selection's right edge
  when not extending). -/
  | wordRight (extend : Bool := false)
  /-- Caret to the start of the (single-line) text. -/
  | home (extend : Bool := false)
  /-- Caret to the end of the (single-line) text. -/
  | «end» (extend : Bool := false)
  /-- Select the whole text. -/
  | selectAll
  /-- Select the word run at byte `off` (double-click). -/
  | selectWord (off : Nat)
  /-- Set the selection directly (offsets snapped to boundaries; direction
  preserved — `range.anchor`/`.active` are kept as given). -/
  | setSelection (range : TextRange)
  /-- Replace the composition region (or the selection when none) with
  `text`, marking it as the new composition; `cursor` is the caret's byte
  offset *within* `text`. Empty `text` cancels the composition. Mirrors
  `SetComposingTextCommand`. -/
  | setComposition (text : String) (cursor : Nat)
  /-- Keep the composed text, clear the composition marker. Mirrors
  `FinishComposingTextCommand`. -/
  | commitComposition
  deriving Repr, BEq, Inhabited

namespace TextFieldValue

/-- The selected span of `text` (empty for a caret). -/
def selectedText (v : TextFieldValue) : String :=
  String.Pos.Raw.extract v.text ⟨v.selection.start⟩ ⟨v.selection.«end»⟩

/-- Snap every offset to a codepoint boundary and clamp into the text; an
empty composition range is dropped. Applied by `apply` before every command,
so externally-supplied values never split a codepoint. -/
def normalized (v : TextFieldValue) : TextFieldValue :=
  let snap := Utf8.floor v.text
  { v with
    selection := ⟨snap v.selection.anchor, snap v.selection.active⟩
    composition := v.composition.bind fun c =>
      let c : TextRange := ⟨snap c.anchor, snap c.active⟩
      if c.collapsed then none else some c }

/-- `text` with bytes `[a, b)` replaced by `repl` (offsets on boundaries). -/
private def replaceRange (text : String) (a b : Nat) (repl : String) : String :=
  String.Pos.Raw.extract text ⟨0⟩ ⟨a⟩ ++ repl
    ++ String.Pos.Raw.extract text ⟨b⟩ ⟨text.utf8ByteSize⟩

/-- Delete bytes `[a, b)`, caret to `a`. -/
private def deleteRange (v : TextFieldValue) (a b : Nat) : TextFieldValue :=
  { text := replaceRange v.text a b ""
    selection := .caret a
    composition := none }

/-- Move the caret: extending keeps `anchor` and moves `active`; otherwise
collapse to `target`. -/
private def moveTo (v : TextFieldValue) (target : Nat) (extend : Bool) : TextFieldValue :=
  if extend then { v with selection := ⟨v.selection.anchor, target⟩ }
  else { v with selection := .caret target }

/-- Apply one `EditCommand` (see the command and module docstrings for the
exact semantics). Total and pure; the input is `normalized` first. Mirrors
`androidx.compose.ui.text.input.EditProcessor.apply`. -/
def apply (v : TextFieldValue) (cmd : EditCommand) : TextFieldValue :=
  let v := v.normalized
  -- The region `insert`/`setComposition` replace: the live composition, or
  -- the selection when not composing.
  let replRegion : Nat × Nat :=
    match v.composition with
    | some c => (c.start, c.«end»)
    | none => (v.selection.start, v.selection.«end»)
  match cmd with
  | .insert t =>
    let (a, b) := replRegion
    { text := replaceRange v.text a b t
      selection := .caret (a + t.utf8ByteSize)
      composition := none }
  | .setComposition t cursor =>
    let (a, b) := replRegion
    let text := replaceRange v.text a b t
    if t.isEmpty then
      { text, selection := .caret a, composition := none }
    else
      { text
        selection := .caret (a + Utf8.floor t (min cursor t.utf8ByteSize))
        composition := some ⟨a, a + t.utf8ByteSize⟩ }
  | .commitComposition => { v with composition := none }
  | cmd =>
    -- Everything else finishes an active composition first (marker cleared,
    -- composed text kept) — see the module docstring.
    let v := { v with composition := none }
    let sel := v.selection
    let size := v.text.utf8ByteSize
    match cmd with
    | .backspace =>
      if !sel.collapsed then v.deleteRange sel.start sel.«end»
      else if sel.active > 0 then v.deleteRange (Utf8.prev v.text sel.active) sel.active
      else v
    | .deleteForward =>
      if !sel.collapsed then v.deleteRange sel.start sel.«end»
      else if sel.active < size then v.deleteRange sel.active (Utf8.next v.text sel.active)
      else v
    | .deleteWordBack =>
      if !sel.collapsed then v.deleteRange sel.start sel.«end»
      else v.deleteRange (Utf8.wordLeft v.text sel.active) sel.active
    | .deleteWordForward =>
      if !sel.collapsed then v.deleteRange sel.start sel.«end»
      else v.deleteRange sel.active (Utf8.wordRight v.text sel.active)
    | .deleteSelection =>
      if sel.collapsed then v else v.deleteRange sel.start sel.«end»
    | .left extend =>
      if extend then v.moveTo (Utf8.prev v.text sel.active) true
      else if !sel.collapsed then v.moveTo sel.start false
      else v.moveTo (Utf8.prev v.text sel.active) false
    | .right extend =>
      if extend then v.moveTo (Utf8.next v.text sel.active) true
      else if !sel.collapsed then v.moveTo sel.«end» false
      else v.moveTo (Utf8.next v.text sel.active) false
    | .wordLeft extend =>
      v.moveTo (Utf8.wordLeft v.text (if extend then sel.active else sel.start)) extend
    | .wordRight extend =>
      v.moveTo (Utf8.wordRight v.text (if extend then sel.active else sel.«end»)) extend
    | .home extend => v.moveTo 0 extend
    | .«end» extend => v.moveTo size extend
    | .selectAll => { v with selection := ⟨0, size⟩ }
    | .selectWord off =>
      let (a, b) := Utf8.wordRangeAt v.text off
      { v with selection := ⟨a, b⟩ }
    | .setSelection r =>
      { v with selection := ⟨Utf8.floor v.text r.anchor, Utf8.floor v.text r.active⟩ }
    -- Handled above; repeated for totality.
    | .insert _ | .setComposition _ _ | .commitComposition => v

/-- Fold a command script (test convenience). -/
def applyAll (v : TextFieldValue) (cmds : List EditCommand) : TextFieldValue :=
  cmds.foldl apply v

end TextFieldValue

/-! ## `#guard` suites -/

/-- Shorthand: value with a selection. -/
private def tv (t : String) (anchor active : Nat) : TextFieldValue :=
  { text := t, selection := ⟨anchor, active⟩ }

/-- Shorthand: value with a caret. -/
private def tc (t : String) (caret : Nat) : TextFieldValue := tv t caret caret

-- insert: empty, at caret, replacing a selection (either direction)
#guard (tc "" 0).apply (.insert "hi") == tc "hi" 2
#guard (tc "ab" 1).apply (.insert "X") == tc "aXb" 2
#guard (tv "hello" 1 4).apply (.insert "u") == tc "huo" 2
#guard (tv "hello" 4 1).apply (.insert "u") == tc "huo" 2
#guard (tc "héllo" 3).apply (.insert "日") == tc "hé日llo" 6
-- backspace: caret, at 0, selection, multi-byte
#guard (tc "abc" 2).apply .backspace == tc "ac" 1
#guard (tc "abc" 0).apply .backspace == tc "abc" 0
#guard (tv "abcd" 1 3).apply .backspace == tc "ad" 1
#guard (tc "héllo" 3).apply .backspace == tc "hllo" 1
#guard (tc "a😀b" 5).apply .backspace == tc "ab" 1
#guard (tc "日本語" 9).apply .backspace == tc "日本" 6
-- deleteForward: caret, at end, selection, multi-byte
#guard (tc "abc" 1).apply .deleteForward == tc "ac" 1
#guard (tc "abc" 3).apply .deleteForward == tc "abc" 3
#guard (tv "abcd" 3 1).apply .deleteForward == tc "ad" 1
#guard (tc "héllo" 1).apply .deleteForward == tc "hllo" 1
-- word deletes (selection wins; else word motion)
#guard (tc "foo bar" 7).apply .deleteWordBack == tc "foo " 4
#guard (tc "foo bar" 4).apply .deleteWordBack == tc "bar" 0
#guard (tc "foo bar" 0).apply .deleteWordForward == tc " bar" 0
#guard (tc "foo bar" 3).apply .deleteWordForward == tc "foo" 3
#guard (tv "foo bar" 1 2).apply .deleteWordBack == tc "fo bar" 1
#guard (tc "" 0).apply .deleteWordBack == tc "" 0
-- deleteSelection
#guard (tv "abcd" 1 3).apply .deleteSelection == tc "ad" 1
#guard (tc "abcd" 2).apply .deleteSelection == tc "abcd" 2
-- left/right: steps, edges, selection collapse to the motion side
#guard (tc "abc" 1).apply (.left) == tc "abc" 0
#guard (tc "abc" 0).apply (.left) == tc "abc" 0
#guard (tc "abc" 2).apply (.right) == tc "abc" 3
#guard (tc "abc" 3).apply (.right) == tc "abc" 3
#guard (tv "abcd" 1 3).apply (.left) == tc "abcd" 1     -- collapse, no move
#guard (tv "abcd" 3 1).apply (.left) == tc "abcd" 1
#guard (tv "abcd" 1 3).apply (.right) == tc "abcd" 3
#guard (tv "abcd" 3 1).apply (.right) == tc "abcd" 3
#guard (tc "héllo" 3).apply (.left) == tc "héllo" 1     -- é is one step
#guard (tc "héllo" 1).apply (.right) == tc "héllo" 3
#guard (tc "a😀b" 1).apply (.right) == tc "a😀b" 5
-- shift extension: grows, shrinks through the anchor, both directions
#guard (tc "abcd" 1).apply (.right true) == tv "abcd" 1 2
#guard ((tc "abcd" 1).applyAll [.right true, .right true]) == tv "abcd" 1 3
#guard ((tc "abcd" 2).applyAll [.right true, .left true]) == tc "abcd" 2
#guard ((tc "abcd" 2).applyAll [.left true, .left true]) == tv "abcd" 2 0
#guard ((tc "abcd" 2).applyAll [.right true, .left true, .left true]) == tv "abcd" 2 1
#guard (tc "abcd" 0).apply (.left true) == tc "abcd" 0
-- word motions
#guard (tc "foo bar  baz" 0).apply (.wordRight) == tc "foo bar  baz" 3
#guard (tc "foo bar  baz" 3).apply (.wordRight) == tc "foo bar  baz" 7
#guard (tc "foo bar  baz" 12).apply (.wordLeft) == tc "foo bar  baz" 9
#guard (tc "foo bar  baz" 9).apply (.wordLeft) == tc "foo bar  baz" 4
#guard (tc "foo bar" 5).apply (.wordLeft true) == tv "foo bar" 5 4
#guard (tc "foo bar" 1).apply (.wordRight true) == tv "foo bar" 1 3
-- non-extended word motion moves from the selection's motion-side edge
#guard (tv "foo bar baz" 4 7).apply (.wordLeft) == tc "foo bar baz" 0
#guard (tv "foo bar baz" 4 7).apply (.wordRight) == tc "foo bar baz" 11
-- home/end (+ shift)
#guard (tc "abc" 2).apply (.home) == tc "abc" 0
#guard (tc "abc" 1).apply (.«end») == tc "abc" 3
#guard (tc "abc" 2).apply (.home true) == tv "abc" 2 0
#guard (tc "abc" 1).apply (.«end» true) == tv "abc" 1 3
#guard (tc "" 0).apply (.«end») == tc "" 0
-- selectAll / selectWord
#guard (tc "héllo" 3).apply .selectAll == tv "héllo" 0 6
#guard (tc "" 0).apply .selectAll == tc "" 0
#guard (tc "foo bar" 0).apply (.selectWord 5) == tv "foo bar" 4 7
#guard (tc "foo bar" 0).apply (.selectWord 3) == tv "foo bar" 3 4
#guard (tc "héllo" 0).apply (.selectWord 4) == tv "héllo" 0 6
-- setSelection: snapping mid-codepoint, clamping, direction preserved
#guard (tc "héllo" 0).apply (.setSelection ⟨2, 2⟩) == tc "héllo" 1
#guard (tc "abc" 0).apply (.setSelection ⟨99, 1⟩) == tv "abc" 3 1
#guard (tc "日本語" 0).apply (.setSelection ⟨4, 8⟩) == tv "日本語" 3 6
-- typing replaces selection, selection direction irrelevant
#guard ((tv "hello world" 0 5).apply (.insert "bye")) == tc "bye world" 3
-- composition flows: set → grow → commit-by-insert
#guard (tc "" 0).apply (.setComposition "に" 3)
        == { text := "に", selection := .caret 3, composition := some ⟨0, 3⟩ }
#guard ((tc "" 0).applyAll [.setComposition "に" 3, .setComposition "にほ" 6])
        == { text := "にほ", selection := .caret 6, composition := some ⟨0, 6⟩ }
#guard ((tc "" 0).applyAll [.setComposition "にほん" 9, .insert "日本"]) == tc "日本" 6
-- commitComposition keeps text, clears the marker
#guard ((tc "" 0).applyAll [.setComposition "日" 3, .commitComposition]) == tc "日" 3
-- empty setComposition cancels (removes the composed text)
#guard ((tc "ab" 1).applyAll [.setComposition "x" 1, .setComposition "" 0]) == tc "ab" 1
-- composition replaces the selection first
#guard ((tv "abcd" 1 3).apply (.setComposition "x" 1))
        == { text := "axd", selection := .caret 2, composition := some ⟨1, 2⟩ }
-- composition sits mid-text; relative cursor honored
#guard ((tc "ab" 1).apply (.setComposition "xy" 1))
        == { text := "axyb", selection := .caret 2, composition := some ⟨1, 3⟩ }
-- a motion finishes the composition (text kept, marker cleared)
#guard ((tc "" 0).applyAll [.setComposition "に" 3, .left])
        == tc "に" 0
#guard ((tc "" 0).applyAll [.setComposition "に" 3, .backspace]) == tc "" 0
-- normalization snaps out-of-range/mid-codepoint external state
#guard ({ text := "héllo", selection := ⟨2, 99⟩ } : TextFieldValue).apply (.left)
        == tc "héllo" 1
#guard (tv "" 5 5).apply (.insert "a") == tc "a" 1
-- selectedText
#guard (tv "hello" 1 4).selectedText == "ell"
#guard (tv "héllo" 0 3).selectedText == "hé"
#guard (tc "abc" 2).selectedText == ""

end Compose
