import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Cells formula engine (`Demos/Cells/Engine.lean`)

The pure, `IO`-free, SDL-free core of the 7GUIs **Cells** demo (99×26
spreadsheet). This module owns everything below the UI: cell addressing, the
formula language (parser + AST), evaluation, and a reactive persistent `Sheet`
that propagates edits to dependents in topological order and detects cycles.

7GUIs Cells has no direct Compose counterpart; the reference is the SCells
implementation from the 7GUIs Haskell solutions, extended here with C-style
infix arithmetic.

## Coordinate system

Columns are `A`–`Z` (`Fin 26`, stored as `Nat` 0–25); rows are `1`–`99`
(1-based, matching typical spreadsheet UIs and the SCells reference). `A1` is
the top-left cell.

## Formula language (two syntaxes, freely mixed)

A cell whose input starts with `=` is a formula. Grammar (case-insensitive
references and function names, whitespace-tolerant):

* **Function application** (SCells style): `add sub mul div mod` (binary) and
  `sum prod` (variadic, accept ranges), e.g. `=SUM(A1:B5)`,
  `=add(1, mul(A1, 2))`.
* **Infix arithmetic** (spreadsheet style) with standard precedence:
  `+ -` bind looser than `* / %`, unary minus, parentheses —
  e.g. `=A1+B2*2-3/4`, `=-(A1)`.
* **Atoms**: decimal numbers (`3`, `2.5`, `.5`), cell references (`A1`, `z99`),
  ranges (`A1:B5`, only valid as a function argument), and double-quoted string
  literals (`"hi"`).

Everything is total: the parser never panics and returns `Except ParseError`;
the evaluator returns a `CellValue` that may carry a `CellError`; division and
modulo by zero yield `#DIV/0!` (spreadsheet convention).
-/

namespace Demos.Cells

/-! ## Cell addressing -/

/-- A cell address: column `col` (0–25 ⇒ `A`–`Z`) and 1-based `row` (1–99).
Only in-range addresses are ever constructed by the parser. -/
structure CellRef where
  /-- Column index, 0-based: 0 ⇒ `A`, 25 ⇒ `Z`. -/
  col : Nat
  /-- Row number, 1-based: 1–99. -/
  row : Nat
deriving BEq, Hashable, DecidableEq, Repr, Inhabited

/-- A total order key `row·26 + col`, used to sort change-lists deterministically
(row-major, matching visual reading order). -/
def CellRef.key (r : CellRef) : Nat := r.row * 26 + r.col

/-- The column letter (`A`–`Z`) for this reference. -/
def CellRef.colLetter (r : CellRef) : Char := Char.ofNat (65 + r.col)

/-- Render a reference in `A1` form. -/
def CellRef.toString (r : CellRef) : String := s!"{r.colLetter}{r.row}"

instance : ToString CellRef := ⟨CellRef.toString⟩

/-- Parse a single `A1`-style reference from a whole string, case-insensitively.
Rejects multi-letter columns and rows outside `1–99`. -/
def CellRef.ofString? (s : String) : Option CellRef :=
  match s.toList with
  | c :: rest =>
    if c.isAlpha && !rest.isEmpty && rest.all (·.isDigit) then
      let col := c.toUpper.toNat - 65
      match (String.ofList rest).toNat? with
      | some row => if col < 26 && 1 ≤ row && row ≤ 99 then some ⟨col, row⟩ else none
      | none => none
    else none
  | [] => none

#guard CellRef.toString ⟨0, 1⟩ == "A1"
#guard CellRef.toString ⟨25, 99⟩ == "Z99"
#guard CellRef.ofString? "A1" == some ⟨0, 1⟩
#guard CellRef.ofString? "z99" == some ⟨25, 99⟩          -- case-insensitive
#guard CellRef.ofString? "A100" == none                 -- row out of range
#guard CellRef.ofString? "A0" == none                   -- rows are 1-based
#guard CellRef.ofString? "AB1" == none                  -- single-letter columns only
#guard CellRef.ofString? "1" == none
-- Round-trip over the whole grid.
#guard (List.range 26).all fun c =>
  (List.range 99).all fun r =>
    let ref : CellRef := ⟨c, r + 1⟩
    CellRef.ofString? ref.toString == some ref

/-- A rectangular range, stored normalized so `tl` is the top-left and `br` the
bottom-right corner. -/
structure CellRange where
  /-- Top-left corner (minimum column and row). -/
  tl : CellRef
  /-- Bottom-right corner (maximum column and row). -/
  br : CellRef
deriving BEq, Repr, Inhabited

/-- Build a normalized range from any two corners. -/
def CellRange.of (a b : CellRef) : CellRange :=
  { tl := ⟨min a.col b.col, min a.row b.row⟩, br := ⟨max a.col b.col, max a.row b.row⟩ }

/-- Render a range in `A1:B5` form. -/
def CellRange.toString (rg : CellRange) : String := s!"{rg.tl}:{rg.br}"

instance : ToString CellRange := ⟨CellRange.toString⟩

/-- All cells covered by the range, in row-major order. -/
def CellRange.cells (rg : CellRange) : Array CellRef := Id.run do
  let mut out := #[]
  for row in [rg.tl.row : rg.br.row + 1] do
    for col in [rg.tl.col : rg.br.col + 1] do
      out := out.push ⟨col, row⟩
  return out

#guard (CellRange.of ⟨0, 1⟩ ⟨1, 2⟩).cells == #[⟨0,1⟩, ⟨1,1⟩, ⟨0,2⟩, ⟨1,2⟩]
#guard (CellRange.of ⟨1, 2⟩ ⟨0, 1⟩).cells == #[⟨0,1⟩, ⟨1,1⟩, ⟨0,2⟩, ⟨1,2⟩]  -- normalized
#guard (CellRange.of ⟨0, 1⟩ ⟨0, 5⟩).cells.size == 5
#guard CellRange.toString (CellRange.of ⟨0, 1⟩ ⟨1, 5⟩) == "A1:B5"

/-! ## Formula AST -/

/-- The five infix / named binary arithmetic operators. -/
inductive BinOp
  | add | sub | mul | div | mod
deriving BEq, Repr, Inhabited

/-- A parsed formula expression. `range` is only produced as a function
argument; evaluating a bare range yields a reference error. -/
inductive Expr
  /-- Numeric literal. -/
  | num (v : Float)
  /-- String literal (double-quoted in source). -/
  | text (s : String)
  /-- A cell reference. -/
  | ref (r : CellRef)
  /-- A cell range (function-argument position only). -/
  | range (r : CellRange)
  /-- Function application, e.g. `sum(A1:B5)`; `name` is lower-cased. -/
  | app (name : String) (args : Array Expr)
  /-- Unary negation. -/
  | neg (e : Expr)
  /-- Infix binary operation. -/
  | binop (op : BinOp) (l r : Expr)
deriving BEq, Repr, Inhabited

/-- The set of function names the parser accepts. -/
def knownFunctions : List String := ["add", "sub", "mul", "div", "mod", "sum", "prod"]

/-! ## Parser

A hand-rolled tokenizer + recursive-descent parser over a `Char` array. Both
phases are total and report a `ParseError` with a source position instead of
panicking. -/

/-- A parse failure: 0-based character `pos` in the formula body (after the
leading `=`), plus a human-readable message. -/
structure ParseError where
  /-- Character offset within the formula body where parsing failed. -/
  pos : Nat
  /-- Human-readable description. -/
  msg : String
deriving BEq, Repr, Inhabited

/-- Lexical tokens. `eof` is a sentinel appended at the end of the stream so the
parser can always peek. -/
inductive Tok
  | num (v : Float)
  | ident (s : String)
  | cref (r : CellRef)
  | str (s : String)
  | lparen | rparen | comma | colon
  | plus | minus | star | slash | percent
  | eof
deriving BEq, Repr, Inhabited

/-- A token paired with its start position. -/
structure PTok where
  /-- The token. -/
  tok : Tok
  /-- Start offset in the source. -/
  pos : Nat
deriving Repr, Inhabited

/-- `10 ^ n` as a `Float`, by repeated multiplication (avoids `HPow` ambiguity). -/
private def pow10 (n : Nat) : Float := Id.run do
  let mut acc := 1.0
  for _ in [0:n] do
    acc := acc * 10.0
  return acc

/-- Consume characters while `p` holds, returning the run and the next index. -/
private partial def readWhile (chars : Array Char) (p : Char → Bool)
    (i : Nat) (acc : String) : String × Nat :=
  match chars[i]? with
  | some c => if p c then readWhile chars p (i + 1) (acc.push c) else (acc, i)
  | none => (acc, i)

/-- Read a decimal number (`123`, `1.5`, `.5`, `5.`) starting at `i`. -/
private def readNumber (chars : Array Char) (i : Nat) : Except ParseError (Float × Nat) :=
  let (intS, j) := readWhile chars (·.isDigit) i ""
  if chars[j]? == some '.' then
    let (fracS, k) := readWhile chars (·.isDigit) (j + 1) ""
    if intS.isEmpty && fracS.isEmpty then
      .error ⟨i, "malformed number"⟩
    else
      let intV := (intS.toNat?.getD 0).toFloat
      let fracV := if fracS.isEmpty then 0.0
                   else (fracS.toNat?.getD 0).toFloat / pow10 fracS.length
      .ok (intV + fracV, k)
  else if intS.isEmpty then
    .error ⟨i, "malformed number"⟩
  else
    .ok ((intS.toNat?.getD 0).toFloat, j)

/-- Read a double-quoted string body (opening quote already consumed). -/
private partial def readString (chars : Array Char) (i : Nat) (acc : String) :
    Except ParseError (String × Nat) :=
  match chars[i]? with
  | some '"' => .ok (acc, i + 1)
  | some c => readString chars (i + 1) (acc.push c)
  | none => .error ⟨i, "unterminated string literal"⟩

/-- Turn a formula body into a token stream terminated by `eof`. -/
private partial def tokenize (chars : Array Char) : Except ParseError (Array PTok) :=
  let rec go (i : Nat) (acc : Array PTok) : Except ParseError (Array PTok) :=
    match chars[i]? with
    | none => .ok (acc.push ⟨.eof, i⟩)
    | some c =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
        go (i + 1) acc
      else if c == '(' then go (i + 1) (acc.push ⟨.lparen, i⟩)
      else if c == ')' then go (i + 1) (acc.push ⟨.rparen, i⟩)
      else if c == ',' then go (i + 1) (acc.push ⟨.comma, i⟩)
      else if c == ':' then go (i + 1) (acc.push ⟨.colon, i⟩)
      else if c == '+' then go (i + 1) (acc.push ⟨.plus, i⟩)
      else if c == '-' then go (i + 1) (acc.push ⟨.minus, i⟩)
      else if c == '*' then go (i + 1) (acc.push ⟨.star, i⟩)
      else if c == '/' then go (i + 1) (acc.push ⟨.slash, i⟩)
      else if c == '%' then go (i + 1) (acc.push ⟨.percent, i⟩)
      else if c == '"' then
        match readString chars (i + 1) "" with
        | .ok (s, j) => go j (acc.push ⟨.str s, i⟩)
        | .error e => .error e
      else if c.isDigit || c == '.' then
        match readNumber chars i with
        | .ok (v, j) => go j (acc.push ⟨.num v, i⟩)
        | .error e => .error e
      else if c.isAlpha then
        let (word, j) := readWhile chars (·.isAlpha) i ""
        -- A single letter immediately followed by a digit is a cell reference;
        -- anything else is a function-name identifier.
        if word.length == 1 && (chars[j]?.any (·.isDigit)) then
          let (digits, k) := readWhile chars (·.isDigit) j ""
          match digits.toNat? with
          | some rowN =>
            if 1 ≤ rowN && rowN ≤ 99 then
              go k (acc.push ⟨.cref ⟨word.toList[0]!.toUpper.toNat - 65, rowN⟩, i⟩)
            else .error ⟨i, s!"row out of range (1–99): {rowN}"⟩
          | none => .error ⟨i, "malformed cell reference"⟩
        else
          go j (acc.push ⟨.ident word.toLower, i⟩)
      else
        .error ⟨i, s!"unexpected character '{c}'"⟩
  go 0 #[]

/-- Peek the token at index `i` (`eof` if past the end). -/
private def peekTok (toks : Array PTok) (i : Nat) : Tok :=
  (toks[i]?).map (·.tok) |>.getD .eof

/-- Source position of the token at index `i`. -/
private def posAt (toks : Array PTok) (i : Nat) : Nat :=
  (toks[i]?).map (·.pos) |>.getD 0

mutual
  /-- `expr := term (('+'|'-') term)*` -/
  private partial def parseExpr (toks : Array PTok) (i : Nat) :
      Except ParseError (Expr × Nat) := do
    let (l, j) ← parseTerm toks i
    parseExprTail toks j l
  /-- Left-associative `+`/`-` continuation. -/
  private partial def parseExprTail (toks : Array PTok) (i : Nat) (l : Expr) :
      Except ParseError (Expr × Nat) := do
    match peekTok toks i with
    | .plus => let (r, k) ← parseTerm toks (i + 1); parseExprTail toks k (.binop .add l r)
    | .minus => let (r, k) ← parseTerm toks (i + 1); parseExprTail toks k (.binop .sub l r)
    | _ => .ok (l, i)
  /-- `term := factor (('*'|'/'|'%') factor)*` -/
  private partial def parseTerm (toks : Array PTok) (i : Nat) :
      Except ParseError (Expr × Nat) := do
    let (l, j) ← parseFactor toks i
    parseTermTail toks j l
  /-- Left-associative `*`/`/`/`%` continuation. -/
  private partial def parseTermTail (toks : Array PTok) (i : Nat) (l : Expr) :
      Except ParseError (Expr × Nat) := do
    match peekTok toks i with
    | .star => let (r, k) ← parseFactor toks (i + 1); parseTermTail toks k (.binop .mul l r)
    | .slash => let (r, k) ← parseFactor toks (i + 1); parseTermTail toks k (.binop .div l r)
    | .percent => let (r, k) ← parseFactor toks (i + 1); parseTermTail toks k (.binop .mod l r)
    | _ => .ok (l, i)
  /-- `factor := '-' factor | atom` -/
  private partial def parseFactor (toks : Array PTok) (i : Nat) :
      Except ParseError (Expr × Nat) := do
    match peekTok toks i with
    | .minus => let (e, j) ← parseFactor toks (i + 1); .ok (.neg e, j)
    | _ => parseAtom toks i
  /-- `atom := number | string | ref [':' ref] | ident '(' args ')' | '(' expr ')'` -/
  private partial def parseAtom (toks : Array PTok) (i : Nat) :
      Except ParseError (Expr × Nat) := do
    match peekTok toks i with
    | .num v => .ok (.num v, i + 1)
    | .str s => .ok (.text s, i + 1)
    | .cref r =>
      match peekTok toks (i + 1) with
      | .colon =>
        match peekTok toks (i + 2) with
        | .cref r2 => .ok (.range (CellRange.of r r2), i + 3)
        | _ => .error ⟨posAt toks (i + 2), "expected cell reference after ':'"⟩
      | _ => .ok (.ref r, i + 1)
    | .ident name =>
      match peekTok toks (i + 1) with
      | .lparen =>
        if knownFunctions.contains name then
          let (args, j) ← parseArgs toks (i + 2)
          .ok (.app name args, j)
        else .error ⟨posAt toks i, s!"unknown function '{name}'"⟩
      | _ => .error ⟨posAt toks i, s!"'{name}' is not a valid cell reference or function call"⟩
    | .lparen =>
      let (e, j) ← parseExpr toks (i + 1)
      match peekTok toks j with
      | .rparen => .ok (e, j + 1)
      | _ => .error ⟨posAt toks j, "expected ')'"⟩
    | .eof => .error ⟨posAt toks i, "unexpected end of formula"⟩
    | _ => .error ⟨posAt toks i, "unexpected token"⟩
  /-- `args := ε | expr (',' expr)*` followed by `')'`. -/
  private partial def parseArgs (toks : Array PTok) (i : Nat) :
      Except ParseError (Array Expr × Nat) := do
    match peekTok toks i with
    | .rparen => .ok (#[], i + 1)
    | _ =>
      let (a, j) ← parseExpr toks i
      parseArgsTail toks j #[a]
  /-- Continuation gathering comma-separated arguments until `')'`. -/
  private partial def parseArgsTail (toks : Array PTok) (i : Nat) (acc : Array Expr) :
      Except ParseError (Array Expr × Nat) := do
    match peekTok toks i with
    | .comma => let (a, k) ← parseExpr toks (i + 1); parseArgsTail toks k (acc.push a)
    | .rparen => .ok (acc, i + 1)
    | _ => .error ⟨posAt toks i, "expected ',' or ')'"⟩
end

/-- Parse a formula **body** (the text after the leading `=`) into an `Expr`.
Requires the whole input to be consumed. -/
def parseFormula (body : String) : Except ParseError Expr := do
  let toks ← tokenize body.toList.toArray
  let (e, j) ← parseExpr toks 0
  match peekTok toks j with
  | .eof => .ok e
  | _ => .error ⟨posAt toks j, "unexpected trailing input"⟩

#guard (parseFormula "42").toOption == some (.num 42.0)
#guard (parseFormula "A1").toOption == some (.ref ⟨0, 1⟩)
#guard (parseFormula "z99").toOption == some (.ref ⟨25, 99⟩)
#guard (parseFormula "SUM(A1:B5)").toOption == some (.app "sum" #[.range (CellRange.of ⟨0,1⟩ ⟨1,5⟩)])
#guard (parseFormula "add(1, mul(A1, 2))").toOption
  == some (.app "add" #[.num 1.0, .app "mul" #[.ref ⟨0,1⟩, .num 2.0]])
-- Precedence: A1 + (B2 * 2) - (3 / 4)
#guard (parseFormula "A1+B2*2-3/4").toOption
  == some (.binop .sub
            (.binop .add (.ref ⟨0,1⟩) (.binop .mul (.ref ⟨1,2⟩) (.num 2.0)))
            (.binop .div (.num 3.0) (.num 4.0)))
-- Parentheses override precedence.
#guard (parseFormula "(A1+B2)*2").toOption
  == some (.binop .mul (.binop .add (.ref ⟨0,1⟩) (.ref ⟨1,2⟩)) (.num 2.0))
#guard (parseFormula "-A1").toOption == some (.neg (.ref ⟨0,1⟩))
#guard (parseFormula "-(A1+1)").toOption == some (.neg (.binop .add (.ref ⟨0,1⟩) (.num 1.0)))
#guard (parseFormula "1 + 2 * 3").toOption == (parseFormula "1+2*3").toOption  -- whitespace tolerant
#guard (parseFormula ".5").toOption == some (.num 0.5)
#guard (parseFormula "PROD()").toOption == some (.app "prod" #[])             -- empty arg list
-- Error cases each yield a ParseError, never a crash:
#guard (parseFormula "").toOption == none                         -- empty formula
#guard (parseFormula "SUM(").toOption == none                     -- unterminated call
#guard (parseFormula "1+").toOption == none                       -- dangling operator
#guard (parseFormula "A100").toOption == none                     -- row out of range
#guard (parseFormula "foo(1)").toOption == none                   -- unknown function
#guard (parseFormula "1 2").toOption == none                      -- trailing input
#guard (parseFormula "(1").toOption == none                       -- missing ')'
#guard (parseFormula "#").toOption == none                        -- unexpected character

/-! ## Cell content -/

/-- What a user typed into a cell, after classification. `formula` keeps both the
original source (for re-editing) and its parsed `Expr`; `badFormula` keeps the
source and the `ParseError` so the cell can display `#ERR!` yet round-trip. -/
inductive CellContent
  /-- Blank cell. -/
  | empty
  /-- Plain text (non-numeric, non-formula input). -/
  | text (s : String)
  /-- A numeric literal. -/
  | number (v : Float)
  /-- A well-formed formula: original `source` (including `=`) and its `expr`. -/
  | formula (source : String) (expr : Expr)
  /-- A formula that failed to parse: original `source` and the error. -/
  | badFormula (source : String) (err : ParseError)
deriving Repr, Inhabited

/-- Parse a bare numeric literal (optionally signed, whitespace-trimmed).
`none` if the whole string is not a number. -/
def parseLiteralNumber (s : String) : Option Float :=
  let trimmed := s.toList.dropWhile (· == ' ') |>.reverse.dropWhile (· == ' ') |>.reverse
  match trimmed with
  | [] => none
  | c :: rest =>
    let (neg, digits) := if c == '-' then (true, rest) else (false, trimmed)
    let arr := digits.toArray
    match readNumber arr 0 with
    | .ok (v, j) => if j == arr.size then some (if neg then -v else v) else none
    | .error _ => none

#guard parseLiteralNumber "42" == some 42.0
#guard parseLiteralNumber "-3.5" == some (-3.5)
#guard parseLiteralNumber "  7 " == some 7.0
#guard parseLiteralNumber "42abc" == none
#guard parseLiteralNumber "" == none

/-- Classify a raw editor input string into `CellContent`. Inputs starting with
`=` are formulas (parsed, or `badFormula` on error); otherwise a numeric literal
becomes `number`, and anything else `text`. -/
def CellContent.ofInput (input : String) : CellContent :=
  match input.toList with
  | [] => .empty
  | c :: rest =>
    if c == '=' then
      match parseFormula (String.ofList rest) with
      | .ok e => .formula input e
      | .error err => .badFormula input err
    else match parseLiteralNumber input with
      | some v => .number v
      | none => .text input

#guard (match CellContent.ofInput "=A1" with | .formula _ e => e == .ref ⟨0,1⟩ | _ => false)
#guard (match CellContent.ofInput "3.5" with | .number v => v == 3.5 | _ => false)
#guard (match CellContent.ofInput "hi" with | .text s => s == "hi" | _ => false)
#guard (match CellContent.ofInput "=1+" with | .badFormula _ _ => true | _ => false)
#guard (match CellContent.ofInput "" with | .empty => true | _ => false)

/-! ## Values and evaluation -/

/-- Why a cell failed to produce a value. Rendered by `displayError`. -/
inductive CellError
  /-- The formula did not parse (`#ERR!`). -/
  | parseError
  /-- The cell is part of a dependency cycle (`#CYCLE!`). -/
  | cycle
  /-- A range was used where a scalar value was required (`#REF!`). -/
  | badRef
  /-- Arithmetic was attempted on text (`#VAL!`). -/
  | typeError
  /-- Division or modulo by zero (`#DIV/0!`). -/
  | divByZero
deriving BEq, Repr, Inhabited

/-- The computed value of a cell. `empty` is the value of a blank cell (it
coerces to `0` in arithmetic and is skipped by aggregates). -/
inductive CellValue
  /-- Blank. -/
  | empty
  /-- A number. -/
  | num (v : Float)
  /-- Text. -/
  | text (s : String)
  /-- An error. -/
  | error (e : CellError)
deriving BEq, Repr, Inhabited

/-- Coerce a value to a number for arithmetic: `empty ⇒ 0`, text ⇒ type error,
errors propagate. -/
private def toNum : CellValue → Except CellError Float
  | .num v => .ok v
  | .empty => .ok 0.0
  | .text _ => .error .typeError
  | .error e => .error e

/-- Floored modulo (result carries the divisor's sign), matching spreadsheet
`MOD`. -/
private def fmod (x y : Float) : Float := x - y * (x / y).floor

/-- Apply a binary operator to two values, propagating errors and coercions. -/
private def binApply (op : BinOp) (a b : CellValue) : CellValue :=
  match toNum a, toNum b with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok x, .ok y =>
    match op with
    | .add => .num (x + y)
    | .sub => .num (x - y)
    | .mul => .num (x * y)
    | .div => if y == 0.0 then .error .divByZero else .num (x / y)
    | .mod => if y == 0.0 then .error .divByZero else .num (fmod x y)

mutual
  /-- Evaluate an expression given a `lookup` for cell references. Pure and
  total; the reactive `Sheet` supplies a `lookup` backed by cached values. -/
  partial def evalExpr (lookup : CellRef → CellValue) : Expr → CellValue
    | .num v => .num v
    | .text s => .text s
    | .ref r => lookup r
    | .range _ => .error .badRef          -- a bare range is not a scalar value
    | .neg e => match toNum (evalExpr lookup e) with
                | .ok x => .num (-x)
                | .error er => .error er
    | .binop op l r => binApply op (evalExpr lookup l) (evalExpr lookup r)
    | .app name args => evalApp lookup name args
  /-- Evaluate a function application. -/
  partial def evalApp (lookup : CellRef → CellValue) (name : String) (args : Array Expr) :
      CellValue :=
    let arith (op : BinOp) : CellValue :=
      if args.size == 2 then binApply op (evalExpr lookup args[0]!) (evalExpr lookup args[1]!)
      else .error .typeError               -- wrong arity
    match name with
    | "add" => arith .add
    | "sub" => arith .sub
    | "mul" => arith .mul
    | "div" => arith .div
    | "mod" => arith .mod
    | "sum" => match foldNums lookup args with
               | .ok xs => .num (xs.foldl (· + ·) 0.0)
               | .error e => .error e
    | "prod" => match foldNums lookup args with
                | .ok xs => .num (xs.foldl (· * ·) 1.0)
                | .error e => .error e
    | _ => .error .typeError               -- unreachable: parser rejects unknown names
  /-- Flatten aggregate arguments into a number list: ranges expand, numbers are
  kept, blanks and text are skipped, and the first error short-circuits. -/
  partial def foldNums (lookup : CellRef → CellValue) (args : Array Expr) :
      Except CellError (Array Float) := do
    let mut acc : Array Float := #[]
    for a in args do
      match a with
      | .range rg =>
        for c in rg.cells do
          match lookup c with
          | .num v => acc := acc.push v
          | .empty => pure ()
          | .text _ => pure ()
          | .error e => throw e
      | _ =>
        match evalExpr lookup a with
        | .num v => acc := acc.push v
        | .empty => pure ()
        | .text _ => pure ()
        | .error e => throw e
    return acc
end

/-- Collect every cell reference an expression reads (ranges expand to all their
cells). Used to build the dependency graph. -/
partial def Expr.refs (e : Expr) : Std.HashSet CellRef :=
  go e {}
where
  go : Expr → Std.HashSet CellRef → Std.HashSet CellRef
  | .num _, s => s
  | .text _, s => s
  | .ref r, s => s.insert r
  | .range rg, s => rg.cells.foldl (·.insert ·) s
  | .neg e, s => go e s
  | .binop _ l r, s => go r (go l s)
  | .app _ args, s => args.foldl (fun acc a => go a acc) s

/-- A small lookup for evaluation tests: A1 = 5, B2 = 10, C1 = "hi". -/
private def testLookup : CellRef → CellValue
  | ⟨0, 1⟩ => .num 5.0
  | ⟨1, 2⟩ => .num 10.0
  | ⟨2, 1⟩ => .text "hi"
  | _ => .empty

/-- Evaluate a formula body string against `lookup` (test helper). -/
private def evalStr (lookup : CellRef → CellValue) (body : String) : CellValue :=
  match parseFormula body with
  | .ok e => evalExpr lookup e
  | .error _ => .error .parseError

#guard evalStr testLookup "1+2*3" == .num 7.0
#guard evalStr testLookup "A1+B2*2-3/4" == .num (5.0 + 10.0*2.0 - 3.0/4.0)   -- 24.25
#guard evalStr testLookup "(A1+B2)*2" == .num 30.0
#guard evalStr testLookup "-A1" == .num (-5.0)
#guard evalStr testLookup "add(1, mul(A1, 2))" == .num 11.0
#guard evalStr testLookup "SUM(A1:B2)" == .num 15.0                -- A1=5,B2=10; blanks skipped
#guard evalStr testLookup "sum(A1, B2, 100)" == .num 115.0
#guard evalStr testLookup "prod(A1, B2)" == .num 50.0
#guard evalStr testLookup "sum(C1, A1)" == .num 5.0               -- text skipped in aggregate
#guard evalStr testLookup "C1+1" == .error .typeError            -- arithmetic on text
#guard evalStr testLookup "1/0" == .error .divByZero
#guard evalStr testLookup "5%0" == .error .divByZero
#guard evalStr testLookup "mod(7, 3)" == .num 1.0
#guard evalStr testLookup "A1:B2" == .error .badRef              -- bare range as value
#guard evalStr testLookup "Z9" == .empty                         -- blank cell
#guard evalStr testLookup "add(1)" == .error .typeError          -- wrong arity
#guard (Expr.refs (.binop .add (.ref ⟨0,1⟩) (.ref ⟨1,2⟩))).toList.length == 2
#guard (match parseFormula "SUM(A1:A3)" with
        | .ok e => e.refs.toList.length == 3 | _ => false)

/-! ## Display formatting -/

/-- Format a float the way a spreadsheet cell shows it: integers without a
decimal point, otherwise trailing zeros trimmed (`42`, `42.5`, not `42.000000`). -/
def formatFloat (v : Float) : String :=
  if v.isNaN then "#ERR!"
  else if !v.isFinite then (if v < 0.0 then "-∞" else "∞")
  else
    let s := toString v
    if s.any (fun c => c == 'e' || c == 'E') then s
    else match s.splitOn "." with
      | [intPart, fracPart] =>
        let frac := fracPart.toList.reverse.dropWhile (· == '0') |>.reverse
        if frac.isEmpty then intPart else intPart ++ "." ++ String.ofList frac
      | _ => s

#guard formatFloat 42.0 == "42"
#guard formatFloat 42.5 == "42.5"
#guard formatFloat (-3.25) == "-3.25"
#guard formatFloat 0.0 == "0"
#guard formatFloat 100.0 == "100"

/-- Render a `CellError` as its spreadsheet display code. -/
def displayError : CellError → String
  | .parseError => "#ERR!"
  | .cycle => "#CYCLE!"
  | .badRef => "#REF!"
  | .typeError => "#VAL!"
  | .divByZero => "#DIV/0!"

/-- Render a `CellValue` as the string shown in a cell. -/
def CellValue.display : CellValue → String
  | .empty => ""
  | .num v => formatFloat v
  | .text s => s
  | .error e => displayError e

#guard CellValue.display (.num 42.0) == "42"
#guard CellValue.display (.error .cycle) == "#CYCLE!"
#guard CellValue.display .empty == ""

/-! ## The reactive sheet

A persistent spreadsheet. Each occupied cell carries its content, cached value,
and the two halves of its dependency edges (`deps` = cells it reads,
`dependents` = cells that read it). `HashMap`/`HashSet` are used for O(1)
functional lookup/update; their persistent (immutable) update semantics make
`Sheet` a value type. Edits recompute only the dirty closure (the changed cell
plus its transitive dependents) in dependency order, so a 1000-cell chain
updates in time linear in the affected cells, not the whole sheet. -/

/-- Per-cell record stored in the sheet. -/
structure CellState where
  /-- The cell's content. -/
  content : CellContent := .empty
  /-- The last computed value. -/
  value : CellValue := .empty
  /-- Cells this cell reads (its dependencies). -/
  deps : Std.HashSet CellRef := {}
  /-- Cells that read this cell (its dependents). -/
  dependents : Std.HashSet CellRef := {}
deriving Inhabited

/-- A spreadsheet: a persistent map from address to `CellState`. Cells absent
from the map are blank. -/
structure Sheet where
  /-- Occupied cells. -/
  cells : Std.HashMap CellRef CellState := {}
deriving Inhabited

/-- The empty sheet. -/
def Sheet.empty : Sheet := {}

/-- The `CellState` at `ref` (a fresh blank state if absent). -/
def Sheet.stateAt (s : Sheet) (ref : CellRef) : CellState :=
  s.cells.getD ref {}

/-- The current value at `ref` (`.empty` if blank). -/
def Sheet.get (s : Sheet) (ref : CellRef) : CellValue :=
  (s.cells.get? ref).map (·.value) |>.getD .empty

/-- The original input string shown in the editor for `ref`. -/
def Sheet.sourceOf (s : Sheet) (ref : CellRef) : String :=
  match (s.cells.get? ref).map (·.content) |>.getD .empty with
  | .empty => ""
  | .text t => t
  | .number v => formatFloat v
  | .formula src _ => src
  | .badFormula src _ => src

/-- The formatted value shown in the grid for `ref`. -/
def Sheet.displayOf (s : Sheet) (ref : CellRef) : String := (s.get ref).display

/-- References read by a piece of content (empty for non-formulas / parse errors). -/
private def CellContent.deps : CellContent → Std.HashSet CellRef
  | .formula _ e => e.refs
  | _ => {}

/-- Recompute-time state: memoized results and the DFS cycle-detection stack. -/
private structure Recompute where
  /-- Values computed so far this pass. -/
  memo : Std.HashMap CellRef CellValue := {}
  /-- Cells currently on the DFS stack (for cycle detection). -/
  visiting : Std.HashSet CellRef := {}

/-- Compute the value of `ref` on demand, memoizing and detecting cycles.
Non-dirty cells return their cached value; a reference reached while already on
the DFS stack yields `#CYCLE!`. -/
private partial def computeRef (sheet : Sheet) (dirty : Std.HashSet CellRef)
    (ref : CellRef) : StateM Recompute CellValue := do
  if let some v := (← get).memo.get? ref then
    return v
  if !dirty.contains ref then
    -- Stable cell: its cached value is authoritative.
    let v := sheet.get ref
    modify fun st => { st with memo := st.memo.insert ref v }
    return v
  if (← get).visiting.contains ref then
    -- Reached a cell already on the DFS stack: this is a genuine cycle. Record it
    -- so the caller's lookup observes `#CYCLE!` (the placeholder is overwritten
    -- with the same value when this cell's own computation completes).
    modify fun st => { st with memo := st.memo.insert ref (.error .cycle) }
    return .error .cycle
  modify fun st => { st with visiting := st.visiting.insert ref }
  let state := sheet.stateAt ref
  let v ← match state.content with
    | .empty => pure .empty
    | .number x => pure (.num x)
    | .text s => pure (.text s)
    | .badFormula _ _ => pure (.error .parseError)
    | .formula _ e =>
      -- Ensure every dependency is computed, then evaluate against the memo.
      for d in state.deps.toList do
        let _ ← computeRef sheet dirty d
      let memo := (← get).memo
      let lookup := fun k => (memo.get? k).getD (sheet.get k)
      pure (evalExpr lookup e)
  modify fun st =>
    { memo := st.memo.insert ref v, visiting := st.visiting.erase ref }
  return v

/-- Recompute every dirty cell, returning a memo of their new values. -/
private def recomputeAll (sheet : Sheet) (dirty : Std.HashSet CellRef) :
    Std.HashMap CellRef CellValue :=
  let act : StateM Recompute Unit := do
    for r in dirty.toList do
      let _ ← computeRef sheet dirty r
  (act.run {}).2.memo

/-- The dirty closure: `start` plus all its transitive dependents. -/
private partial def dirtyClosure (sheet : Sheet) (start : CellRef) : Std.HashSet CellRef :=
  go [start] {}
where
  go : List CellRef → Std.HashSet CellRef → Std.HashSet CellRef
  | [], seen => seen
  | r :: rest, seen =>
    if seen.contains r then go rest seen
    else
      let seen := seen.insert r
      let deps := (sheet.stateAt r).dependents.toList
      go (deps ++ rest) seen

/-- Insert `who` into the `dependents` of every cell in `targets`. -/
private def addDependentEdges (cells : Std.HashMap CellRef CellState)
    (who : CellRef) (targets : Std.HashSet CellRef) : Std.HashMap CellRef CellState :=
  targets.fold (fun m t =>
    let st := m.getD t {}
    m.insert t { st with dependents := st.dependents.insert who }) cells

/-- Remove `who` from the `dependents` of every cell in `targets`. -/
private def removeDependentEdges (cells : Std.HashMap CellRef CellState)
    (who : CellRef) (targets : Std.HashSet CellRef) : Std.HashMap CellRef CellState :=
  targets.fold (fun m t =>
    let st := m.getD t {}
    m.insert t { st with dependents := st.dependents.erase who }) cells

/-- Set `ref`'s input and recompute the affected cells, returning the new sheet
**and** the array of references whose displayed value changed (sorted in
row-major order). Cells whose recomputed value equals their previous value are
omitted — the value-equality cutoff that lets the UI invalidate exactly what
changed. Cycles produce `#CYCLE!` and recover automatically once broken. -/
def Sheet.setD (sheet : Sheet) (ref : CellRef) (input : String) : Sheet × Array CellRef :=
  let content := CellContent.ofInput input
  let newDeps := content.deps
  let oldState := sheet.stateAt ref
  -- Rewire this cell's dependency edges (its own dependents are untouched).
  let cells := sheet.cells
    |> (removeDependentEdges · ref oldState.deps)
    |> (addDependentEdges · ref newDeps)
  let refState := { cells.getD ref {} with content := content, deps := newDeps }
  let sheet' : Sheet := { cells := cells.insert ref refState }
  -- Recompute the changed cell and everything downstream, in dependency order.
  let dirty := dirtyClosure sheet' ref
  let memo := recomputeAll sheet' dirty
  let (newCells, changed) :=
    dirty.fold (fun (acc : Std.HashMap CellRef CellState × Array CellRef) r =>
      let (cs, ch) := acc
      let newVal := (memo.get? r).getD .empty
      let oldVal := sheet.get r
      let st := cs.getD r {}
      let cs := cs.insert r { st with value := newVal }
      let ch := if newVal == oldVal then ch else ch.push r
      (cs, ch))
    (sheet'.cells, #[])
  ({ cells := newCells }, changed.qsort (·.key < ·.key))

/-- Set `ref`'s input, discarding the change-list (see `Sheet.setD`). -/
def Sheet.set (sheet : Sheet) (ref : CellRef) (input : String) : Sheet :=
  (sheet.setD ref input).1

/-! ### Sheet scenario tests

Small builders drive multi-cell scenarios entirely at compile time. -/

/-- Apply a list of `(reference, input)` edits to the empty sheet. -/
private def build (edits : List (CellRef × String)) : Sheet :=
  edits.foldl (fun s (ref, inp) => s.set ref inp) Sheet.empty

private def a1 : CellRef := ⟨0, 1⟩
private def a2 : CellRef := ⟨0, 2⟩
private def a3 : CellRef := ⟨0, 3⟩
private def a5 : CellRef := ⟨0, 5⟩
private def b1 : CellRef := ⟨1, 1⟩
private def c1 : CellRef := ⟨2, 1⟩
private def d1 : CellRef := ⟨3, 1⟩

-- Chain propagation: A1=1, A2==A1+1, A3==A2+1; editing A1 flows through.
#guard
  let s := build [(a1, "1"), (a2, "=A1+1"), (a3, "=A2+1")]
  s.get a3 == .num 3.0
#guard
  let s := build [(a1, "1"), (a2, "=A1+1"), (a3, "=A2+1")]
  (s.set a1 "10").get a3 == .num 12.0

-- Diamond dependency: D1 reads B1 and C1, both reading A1. Single consistent update.
#guard
  let s := build [(a1, "2"), (b1, "=A1*3"), (c1, "=A1+1"), (d1, "=B1+C1")]
  s.get d1 == .num 9.0
#guard
  let s := build [(a1, "2"), (b1, "=A1*3"), (c1, "=A1+1"), (d1, "=B1+C1")]
  (s.set a1 "10").get d1 == .num 41.0

-- Cycle detection: self-reference, 2-cycle, 3-cycle all report #CYCLE!.
#guard (build [(a1, "=A1")]).get a1 == .error .cycle
#guard
  let s := build [(a1, "=A2+1"), (a2, "=A1+1")]
  s.get a1 == .error .cycle && s.get a2 == .error .cycle
#guard
  let s := build [(a1, "=A2"), (a2, "=A3"), (a3, "=A1")]
  s.get a1 == .error .cycle && s.get a2 == .error .cycle && s.get a3 == .error .cycle
-- Recovery: breaking the cycle restores real values automatically.
#guard
  let s := build [(a1, "=A2+1"), (a2, "=A1+1")]
  let s := s.set a1 "5"
  s.get a1 == .num 5.0 && s.get a2 == .num 6.0

-- Range dependency: SUM(A1:A3) tracks edits to any member, and rebuilds edges
-- when the formula changes.
#guard
  let s := build [(a1, "1"), (a2, "2"), (a3, "3"), (a5, "=SUM(A1:A3)")]
  s.get a5 == .num 6.0
#guard
  let s := build [(a1, "1"), (a2, "2"), (a3, "3"), (a5, "=SUM(A1:A3)")]
  (s.set a3 "30").get a5 == .num 33.0
#guard
  -- Point A5 at a smaller range, then edit a now-irrelevant cell: no effect.
  let s := build [(a1, "1"), (a2, "2"), (a3, "3"), (a5, "=SUM(A1:A3)")]
  let s := s.set a5 "=SUM(A1:A2)"
  s.get a5 == .num 3.0 && (s.set a3 "99").get a5 == .num 3.0

-- Text / number coercion and display formatting through the sheet.
#guard (build [(a1, "hi"), (a2, "=A1+1")]).get a2 == .error .typeError
#guard (build [(a1, "3"), (a2, "=A1")]).displayOf a2 == "3"
#guard (build [(a1, "=1/0")]).displayOf a1 == "#DIV/0!"
#guard (build [(a1, "=A1")]).displayOf a1 == "#CYCLE!"
#guard (build [(a1, "=A1")]).sourceOf a1 == "=A1"                 -- source preserved for re-edit

-- setD change-lists report exactly the cells whose display changed.
#guard
  let s := build [(a1, "1"), (a2, "=A1+1"), (a3, "=A2+1")]
  (s.setD a1 "10").2 == #[a1, a2, a3]                             -- whole chain changed
#guard
  let s := build [(a1, "1"), (a2, "=A1+1"), (a3, "=A2+1")]
  (s.setD a1 "1").2 == #[]                                        -- value unchanged ⇒ empty
#guard
  -- B1 = A1*0 is unaffected by A1's magnitude, so it is *not* reported.
  let s := build [(a1, "1"), (b1, "=A1*0"), (c1, "=A1+1")]
  (s.setD a1 "5").2 == #[a1, c1]

-- Perf / stress (pure, compile-time): a 1000-cell dependency chain updates
-- correctly (and quickly — linear in the chain).
#guard
  -- 20 columns (A–T) × 50 rows = 1000 cells, all within range.
  let refs := (List.range 50).flatMap fun r =>
    (List.range 20).map fun c => (⟨c, r + 1⟩ : CellRef)
  -- refs[0] = 1; each subsequent cell = previous + 1.
  let s := (refs.foldl (fun (acc : Sheet × Option CellRef) ref =>
      let (s, prev) := acc
      match prev with
      | none => (s.set ref "1", some ref)
      | some p => (s.set ref s!"={p}+1", some ref)) (Sheet.empty, none)).1
  s.get refs[999]! == .num 1000.0

end Demos.Cells
