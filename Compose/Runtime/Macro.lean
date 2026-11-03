module

meta import Lean
public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer
public import Compose.Runtime.SkipEq
public meta import Compose.Runtime.SkipEq

namespace Compose

/-!
# The `composable` macro

The Lean answer to Compose's compiler plugin (`@Composable` lowering). Two
syntaxes:

```lean
/-- Optional doc comment. -/
composable def counter (label : String) : Composable Unit := do ...

composable fun item => do ...   -- position-stable content lambda (term)
```

`composable def` rewrites the definition into Compose's restartable,
skippable shape: the body runs inside `startRestartGroup`/`endRestartGroup`
(keyed by a hash of the fully-qualified name), one `Composer.changed` slot per
explicit parameter feeds the `shouldSkip` check (`SkipEq` per argument:
`BEq` types enable skipping, others disable it), and the scope stores a rerun
closure re-invoking the function with the same argument values (a parent
recomposition supplies fresh arguments by re-running the call site).

**Control-flow keying**: the do-block body is traversed and every branch of
`if`/`match` (including `if let` and `else if` chains) and every `for`-loop
body is wrapped in `withGroup k`, `k` a compile-time literal mixed from the
declaration key and the branch's source position — so composition positions
stay stable when a condition flips, exactly like the groups the Compose
compiler plugin injects. `for` bodies get one positional group per iteration
(same key: siblings match positionally; identity across reorder still needs
the explicit `keyed` combinator). A loop body that is a single `keyed …` /
`withGroup …` call is *not* wrapped again: the user's data key is the
iteration group, which is what lets `keyed` preserve state across reorder.

**Boundaries (documented, by design):** the rewriter recurses into nested
transparent `do` blocks, branch bodies, and the right-hand side of
`let x ← …`, but does **not** descend into terms: lambdas, `do` blocks passed
as *arguments* (e.g. the body of a `keyed x do …` call), and `by` proofs keep
their syntax untouched. `composable fun` is the escape hatch for content
lambdas: it wraps the lambda body in a position-keyed group and applies the
same control-flow keying inside (not restartable, not skippable). `while` and
`try` bodies are not keyed either — use the explicit combinator API for those
shapes. Because a wrapped branch becomes its own group (a separate
computation), `return`, `break`, `continue`, and reassignment of a `mut`
variable declared outside the branch are rejected with a macro error instead
of silently changing meaning.

The runtime is fully usable *without* this macro (explicit `withGroup` /
`keyed` / `remember`); the macro is sugar + skippability on top of the frozen
M1 hooks (`startRestartGroup`, `shouldSkip`, `skipToGroupEnd`,
`endRestartGroup`).
-/

public meta section

open Lean

/-- Rewriter state: ordinal counter for `branchKey`. -/
private abbrev RewriteM := StateT Nat MacroM

/-- Key for the branch whose body is (or is near) `stx`. -/
private def nextKey (declKey : UInt64) (stx : Syntax) : RewriteM UInt64 := do
  let ord ← modifyGet fun n => (n, n + 1)
  return branchKey declKey ((stx.getPos?.map (·.byteIdx)).getD 0) ord

/-- `f` applied to child `i` (other children untouched). -/
private def modifyArgM (stx : Syntax) (i : Nat) (f : Syntax → RewriteM Syntax) :
    RewriteM Syntax :=
  return stx.setArg i (← f (stx.getArg i))

/-- All identifier names in `stx` (approximation used for `mut` tracking). -/
private partial def collectIdents (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  if stx.isIdent then acc.push stx.getId
  else stx.getArgs.foldl (fun a s => collectIdents s a) acc

/-- Syntax kinds `checkWrappable` does not look inside: separate computations
(terms) and constructs that receive their own wrap + check during rewriting. -/
private def wrapOpaqueKinds : List Name :=
  [``Lean.Parser.Term.do, ``Lean.Parser.Term.fun, ``Lean.Parser.Term.byTactic,
   ``Lean.Parser.Term.doIf, ``Lean.Parser.Term.doMatch, ``Lean.Parser.Term.doFor,
   ``Lean.Parser.Term.doUnless]

/-- Reject do-elements whose meaning would silently change when the enclosing
statements move into their own group (a separate `do` computation): `return`,
`break`, `continue`, and reassignment of `mut` variables declared outside the
wrapped region. `muts` accumulates the names declared mutable *inside* the
region (reassigning those stays legal). The check is per wrapped region;
nested branches are checked when their own wrap happens. -/
private partial def checkWrappable (muts : Array Name) (stx : Syntax) :
    MacroM (Array Name) := do
  let k := stx.getKind
  if k == ``Lean.Parser.Term.doReturn then
    Macro.throwErrorAt stx
      "`return` is not supported inside composable `if`/`match`/`for` bodies: the \
       branch becomes its own group, so `return` would no longer exit the surrounding \
       composable. Restructure the branch, or use the explicit `withGroup` API."
  else if k == ``Lean.Parser.Term.doBreak || k == ``Lean.Parser.Term.doContinue then
    Macro.throwErrorAt stx
      "`break`/`continue` are not supported inside composable `for` bodies: each \
       iteration becomes its own group. Restructure the loop, or use the explicit \
       `withGroup` API."
  else if k == ``Lean.Parser.Term.doReassign then
    -- (letIdDeclNoBinders target …) — patterns are left to the elaborator.
    let tgt := stx[0][0][0]
    if tgt.isIdent && !muts.contains tgt.getId then
      Macro.throwErrorAt stx
        s!"cannot reassign `{tgt.getId}` here: it is declared outside this composable \
           branch/loop body, which becomes its own group (a separate computation). \
           Declare the `mut` inside the branch, or restructure."
    return muts
  else if k == ``Lean.Parser.Term.doReassignArrow then
    let decl := stx[0]
    if decl.getKind == ``Lean.Parser.Term.doIdDecl then
      let tgt := decl[0]
      if tgt.isIdent && !muts.contains tgt.getId then
        Macro.throwErrorAt stx
          s!"cannot reassign `{tgt.getId}` here: it is declared outside this composable \
             branch/loop body, which becomes its own group (a separate computation). \
             Declare the `mut` inside the branch, or restructure."
      checkWrappable muts decl[3]
    else
      return muts
  else if k == ``Lean.Parser.Term.doLet then
    return if stx[1].getNumArgs > 0 then collectIdents stx[3] muts else muts
  else if k == ``Lean.Parser.Term.doLetArrow then
    let decl := stx[3]
    let muts := if stx[1].getNumArgs > 0 then collectIdents decl[0] muts else muts
    if decl.getKind == ``Lean.Parser.Term.doIdDecl ||
        decl.getKind == ``Lean.Parser.Term.doPatDecl then
      checkWrappable muts decl[3]
    else
      return muts
  else if wrapOpaqueKinds.contains k then
    return muts
  else
    stx.getArgs.foldlM checkWrappable muts

/-- The `doSeqItem` children of a `doSeq`. -/
private def seqItems (seq : Syntax) : Array Syntax :=
  let itemsIdx := if seq.getKind == ``Lean.Parser.Term.doSeqBracketed then 1 else 0
  (seq.getArg itemsIdx).getArgs.filter (·.getKind == ``Lean.Parser.Term.doSeqItem)

/-- Head of an application spine (`f a b` ↦ `f`). -/
private partial def appHead (t : Syntax) : Syntax :=
  if t.getKind == ``Lean.Parser.Term.app then appHead (t.getArg 0) else t

/-- Whether the loop body is a single `keyed …` / `withGroup …` statement, in
which case the user's group *is* the iteration group and no positional wrap is
added (this is what lets `keyed` move state across a reorder). -/
private def isDataKeyedBody (seq : Syntax) : Bool :=
  match seqItems seq with
  | #[item] =>
    let e := item.getArg 0
    e.getKind == ``Lean.Parser.Term.doExpr &&
      (let h := appHead (e.getArg 0)
       h.isIdent &&
         match h.getId.eraseMacroScopes with
         | .str _ s => s == "keyed" || s == "withGroup"
         | _ => false)
  | _ => false

mutual

/-- Rewrite every element of a `doSeq` (leaving non-control-flow statements
untouched). -/
private partial def rewriteSeq (declKey : UInt64) (seq : Syntax) : RewriteM Syntax := do
  let k := seq.getKind
  if k == ``Lean.Parser.Term.doSeqIndent || k == ``Lean.Parser.Term.doSeqBracketed then
    let itemsIdx := if k == ``Lean.Parser.Term.doSeqBracketed then 1 else 0
    modifyArgM seq itemsIdx fun items => do
      let elems ← items.getArgs.mapM fun item => do
        if item.getKind == ``Lean.Parser.Term.doSeqItem then
          modifyArgM item 0 (rewriteElem declKey)
        else
          pure item
      return items.setArgs elems
  else
    return seq

/-- Check, recursively rewrite, then wrap a branch/loop-body `doSeq` in
`Compose.withGroup k (do …)` — the group the Compose compiler plugin would
inject at this source position. -/
private partial def wrapSeq (declKey : UInt64) (seq : Syntax) : RewriteM Syntax := do
  let _ ← (checkWrappable #[] seq : MacroM _)
  let seq' ← rewriteSeq declKey seq
  let key := Lean.quote (← nextKey declKey seq).toNat
  let doTerm : Term := ⟨mkNode ``Lean.Parser.Term.do #[mkAtom "do", seq']⟩
  let call ← `(Compose.withGroup $key $doTerm)
  return mkNode ``Lean.Parser.Term.doSeqIndent #[mkNullNode #[
    mkNode ``Lean.Parser.Term.doSeqItem
      #[mkNode ``Lean.Parser.Term.doExpr #[call.raw], mkNullNode]]]

/-- Rewrite one do-element: key the branches of `if`/`unless`/`match`, wrap
`for` bodies, recurse through transparent nested `do` and the right-hand side
of `let x ← …`; leave everything else untouched. -/
private partial def rewriteElem (declKey : UInt64) (e : Syntax) : RewriteM Syntax := do
  let k := e.getKind
  if k == ``Lean.Parser.Term.doIf then
    -- #["if", cond, "then", thenSeq, elseIfs, else?]
    let e ← modifyArgM e 3 (wrapSeq declKey)
    let e ← modifyArgM e 4 fun elifs => do
      let gs ← elifs.getArgs.mapM (modifyArgM · 3 (wrapSeq declKey))
      return elifs.setArgs gs
    modifyArgM e 5 fun els => do
      if els.getNumArgs == 2 then modifyArgM els 1 (wrapSeq declKey) else pure els
  else if k == ``Lean.Parser.Term.doUnless then
    -- #["unless", cond, "do", seq]
    modifyArgM e 3 (wrapSeq declKey)
  else if k == ``Lean.Parser.Term.doMatch then
    -- #["match", gen, motive, _, discrs, "with", alts]
    modifyArgM e 6 fun alts => modifyArgM alts 0 fun altList => do
      let as ← altList.getArgs.mapM fun alt => do
        if alt.getKind == ``Lean.Parser.Term.matchAlt then
          modifyArgM alt 3 (wrapSeq declKey)   -- #["|", pats, "=>", rhs]
        else
          pure alt
      return altList.setArgs as
  else if k == ``Lean.Parser.Term.doFor then
    -- #["for", decls, invariant?, decreasing?, "do", seq] since Lean 4.35
    -- (#["for", decls, "do", seq] before): the body is always the last child.
    modifyArgM e (e.getNumArgs - 1) fun body => do
      if isDataKeyedBody body then pure body else wrapSeq declKey body
  else if k == ``Lean.Parser.Term.doNested then
    -- #["do", seq] — transparent: recurse without wrapping.
    modifyArgM e 1 (rewriteSeq declKey)
  else if k == ``Lean.Parser.Term.doLetArrow then
    -- #["let", mut?, letConfig, decl] with decl = (doIdDecl _ _ "←" rhs …).
    modifyArgM e 3 (rewriteDecl declKey)
  else if k == ``Lean.Parser.Term.doReassignArrow then
    modifyArgM e 0 (rewriteDecl declKey)
  else
    return e

/-- Recurse into the right-hand side of `doIdDecl`/`doPatDecl` (so
`let x ← if … then … else …` gets keyed branches too). -/
private partial def rewriteDecl (declKey : UInt64) (d : Syntax) : RewriteM Syntax := do
  if d.getKind == ``Lean.Parser.Term.doIdDecl || d.getKind == ``Lean.Parser.Term.doPatDecl then
    modifyArgM d 3 (rewriteElem declKey)
  else
    return d

end

/-- Apply control-flow keying to a composable body: rewrites `do` blocks,
leaves any other term as-is. -/
private def rewriteBody (declKey : UInt64) (body : Term) : MacroM Term := do
  if body.raw.getKind == ``Lean.Parser.Term.do then
    let (seq', _) ← (rewriteSeq declKey (body.raw.getArg 1)).run 0
    return ⟨body.raw.setArg 1 seq'⟩
  else
    return body

/-- Whether the declared result type is (syntactically) `Composable Unit`. -/
private def resultIsComposableUnit (ty : Term) : Bool :=
  match ty.raw with
  | .node _ ``Lean.Parser.Term.app #[fn, .node _ _ #[arg]] =>
    fn.isIdent && arg.isIdent &&
      (let n := fn.getId.eraseMacroScopes
       n == `Composable || n == `Compose.Composable) &&
      arg.getId.eraseMacroScopes == `Unit
  | _ => false

/-- Restartable, skippable composable function — the Lean spelling of
Kotlin's `@Composable fun`. See the module docstring for the full semantics.

```lean
composable def counter (label : String) : Composable Unit := do …
```
-/
syntax (name := composableDef) (docComment)? "composable " "def " declId
  bracketedBinder* " : " term " := " term : command

/-- Position-stable content lambda: wraps the lambda body in a group keyed by
source position (and applies control-flow keying inside). Not restartable,
not skippable — the group form Compose gives composable lambda arguments.

```lean
composable fun item => do …
```
-/
syntax (name := composableFun) "composable " term : term

macro_rules
  | `($[$doc:docComment]? composable def $id:declId $bs:bracketedBinder* : $ty := $body) => do
    unless resultIsComposableUnit ty do
      Macro.throwErrorAt ty
        "composable def: the result type must be `Composable Unit` (restartable \
         composables return `Unit`; other shapes should use the explicit combinator API)"
    let fnStx := id.raw.getArg 0
    unless fnStx.isIdent do
      Macro.throwErrorAt id "composable def: expected a plain declaration name"
    let declName := (← Macro.getCurrNamespace) ++ fnStx.getId.eraseMacroScopes
    let declKey := stringKey declName.toString
    -- Explicit value parameters feed the skip check and the restart closure;
    -- implicit/instance parameters are ignored (re-inferred at the rerun).
    let mut args : Array Ident := #[]
    for b in bs do
      if b.raw.getKind == ``Lean.Parser.Term.explicitBinder then
        for x in (b.raw.getArg 1).getArgs do
          if x.isIdent then
            args := args.push ⟨x⟩
          else
            Macro.throwErrorAt x
              "composable def: explicit parameters must be named (the restart closure \
               re-applies them)"
    let body' ← rewriteBody declKey body
    let key := quote declKey.toNat
    -- All `changed` slots are consumed unconditionally (no short-circuit): each
    -- explicit argument owns one slot in the restart group, in declaration order.
    let changedTerm : Term ← args.foldrM (init := ← `(pure false)) fun a acc =>
      `(do
          let argChanged ← Compose.Composer.changed c $a
          let restChanged ← ($acc)
          pure (argChanged || restChanged))
    let fnId : Ident := ⟨fnStx⟩
    let rerunApp : Term ← if args.isEmpty then pure (fnId : Term) else `($fnId $args*)
    let defBody : Term ← `(fun c => do
      let scope ← Compose.Composer.startRestartGroup c $key
      let argsChanged ← ($changedTerm)
      if ← Compose.Composer.shouldSkip c scope argsChanged then
        Compose.Composer.skipToGroupEnd c
      else
        ReaderT.run ($body' : $ty) c
      Compose.Composer.endRestartGroup c scope (ReaderT.run ($rerunApp : $ty) c))
    match doc with
    | some d => `($d:docComment partial def $id:declId $bs:bracketedBinder* : $ty := $defBody)
    | none => `(partial def $id:declId $bs:bracketedBinder* : $ty := $defBody)

macro_rules
  | `(composable $f) => do
    match f with
    | `(fun $xs* => $body) => do
      let mainMod ← MonadQuotation.getMainModule
      let ns ← Macro.getCurrNamespace
      let pos := (f.raw.getPos?.map (·.byteIdx)).getD 0
      -- The current macro scope is unique per expansion (and deterministic
      -- within a build), so two `composable fun`s with the *same* source
      -- position — position-less macro-generated syntax (`getPos? = none`),
      -- or one user macro expanding to several lambdas — still get distinct
      -- keys. Without it, dynamically switching between two such lambdas at
      -- one composition position would reuse the group and bleed its
      -- remember slots across the switch (slot-type drift = UB).
      let scp ← MonadQuotation.getCurrMacroScope
      let base := mixKeys (stringKey s!"{mainMod}.{ns}")
        (mixKeys pos.toUInt64 scp.toUInt64)
      let body' ← rewriteBody base body
      let key := quote base.toNat
      `(fun $xs* => Compose.withGroup $key $body')
    | _ =>
      Macro.throwErrorAt f
        "`composable` expects a `fun` literal here (e.g. `composable fun item => do …`); \
         for declarations use `composable def`"

end

end Compose
