import Lean
import Compose

/-!
# Compile-time API lint (`test/ComposeTests/ApiLint.lean`)

`#composeApiLint` scans the built environment and enforces the signature
conventions adopted from the Kotlin compose-rules lint set (the subset that is
real here but not enforceable by types; see docs/DESIGN.md "API conventions"):

1. **Modifier**: every public uppercase component (result `Composable Unit`,
   in `Compose.Material`/`Foundation`/`Animation`) takes
   `modifier : Modifier := {}`, unless allowlisted. Any `Modifier` param is
   named `modifier` or `…Modifier`.
2. **Param order**: no required explicit param after a defaulted one.
3. **Content slot**: the last content-like param (codomain `Composable Unit`)
   is the last *required* param or the *first* defaulted param — the two
   placements a trailing `do` block can reach (Lean named-argument adaptation
   of Kotlin's "content literally last").
4. **Events after content**: no event-like param (codomain `IO Unit`) after
   the content slot.
5. **Event naming**: event-like params are named `on…`.
6. **CompositionLocal naming**: `CompositionLocal` constants are `Local…`.
7. **Value composables**: defs returning `Composable α` (`α ≠ Unit`) anywhere
   under `Compose.*` are lowerCamelCase (`remember…`, `animate…AsState`, …).

Violations are elaboration **errors**, so `lake exe test` fails to build; the
runtime check tally is unchanged. The command self-tests first: deliberately
bad private fixtures below must each trip their rule, and a conforming one
must report clean. The `minComponents` floor guards against the scan silently
matching nothing after a refactor.

The `StateInit` remember-gate (compose-rules "RememberMissing") is enforced by
types, not this lint; the `#guard_msgs`/`#check_failure` pins at the bottom
keep its behavior anchored against toolchain bumps.
-/

open Lean Meta Elab Command

namespace Tests.ApiLint
open Compose

/-- Components exempt from the `modifier` rule, with reasons. -/
def modifierAllowlist : List Name :=
  [``Compose.MaterialTheme,   -- non-emitting: a pure CompositionLocalProvider nest
   ``Compose.TooltipSurface,  -- fixed-styled tooltip content piece
   ``Compose.MenuBar,         -- window chrome; Compose Desktop's MenuBar has none either
   ``Compose.BackHandler]     -- non-emitting: registers a back interceptor

/-- Module prefixes scanned for component signature rules (1-5). -/
def componentPrefixes : List Name :=
  [`Compose.Material, `Compose.Foundation, `Compose.Animation]

/-- One explicit value parameter of a scanned declaration. -/
structure Param where
  name : Name
  /-- The parameter type with `optParam`/`autoParam` stripped. -/
  type : Expr
  /-- Has a default value (or tactic). -/
  optional : Bool
  /-- The `optParam` default value, if any. -/
  default? : Option Expr
  deriving Inhabited

/-- The explicit params and result type of `declName`'s signature. -/
def signatureOf (declName : Name) : MetaM (Array Param × Expr) := do
  let ci ← getConstInfo declName
  forallTelescope ci.type fun xs cod => do
    let mut ps := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo.isExplicit do continue
      let t := decl.type.consumeMData
      if t.isOptParam then
        ps := ps.push ⟨decl.userName, t.appFn!.appArg!, true, some t.appArg!⟩
      else if t.isAutoParam then
        ps := ps.push ⟨decl.userName, t.appFn!.appArg!, true, none⟩
      else
        ps := ps.push ⟨decl.userName, t, false, none⟩
    return (ps, cod.cleanupAnnotations)

/-- Is `t` (a codomain) syntactically `Composable Unit`? -/
def isComposableUnit (t : Expr) : Bool :=
  match t with
  | .app (.const ``Compose.Composable _) (.const ``Unit _) => true
  | _ => false

/-- Is `t` syntactically `Composable α` with `α ≠ Unit`? -/
def isComposableValue (t : Expr) : Bool :=
  match t with
  | .app (.const ``Compose.Composable _) a => !a.isConstOf ``Unit
  | _ => false

/-- Strip the argument types off a (possibly 0-ary) function type. -/
partial def codomainOf (t : Expr) : Expr :=
  match t with
  | .forallE _ _ b _ => codomainOf b
  | _ => t

/-- A content slot: the param's codomain is `Composable Unit`
(`content : Composable Unit`, `itemContent : Nat → Composable Unit`).
`Option (Composable Unit)` (optional slots) deliberately doesn't count. -/
def isContentLike (p : Param) : Bool :=
  isComposableUnit (codomainOf p.type).cleanupAnnotations

/-- An event callback: the param's codomain is literally `IO Unit`
(`onClick : IO Unit`, `onValueChange : String → IO Unit`). -/
def isEventLike (p : Param) : Bool :=
  match (codomainOf p.type).cleanupAnnotations with
  | .app (.const ``IO _) (.const ``Unit _) => true
  | _ => false

/-- The last name component, as a string (`""` for numeric components). -/
def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

/-- Rules 1-5 for one component. `defaultMod` is an elaborated
`({} : Modifier)` for the default-value check. -/
def componentViolations (defaultMod : Expr) (declName : Name) : MetaM (List String) := do
  let (ps, _) ← signatureOf declName
  let mut vs : List String := []
  -- 1: modifier param present, typed, defaulted to {}
  unless modifierAllowlist.contains declName do
    match ps.find? (·.name == `modifier) with
    | none => vs := vs ++ ["missing a `modifier : Modifier := {}` parameter"]
    | some p =>
      if !p.type.isConstOf ``Compose.Modifier then
        vs := vs ++ ["`modifier` is not of type `Modifier`"]
      else match p.default? with
        | none => vs := vs ++ ["`modifier` has no `:= {}` default"]
        | some v =>
          unless ← withNewMCtxDepth (isDefEq v defaultMod) do
            vs := vs ++ ["`modifier` default is not `{}`"]
  -- 1b: Modifier params named `modifier` / `…Modifier`
  for p in ps do
    if p.type.isConstOf ``Compose.Modifier then
      let s := p.name.toString
      unless s == "modifier" || s.endsWith "Modifier" do
        vs := vs ++ [s!"`Modifier` param `{p.name}` should be `modifier` or `…Modifier`"]
  -- 2: no required param after a defaulted one
  let mut seenOptional := false
  for p in ps do
    if p.optional then
      seenOptional := true
    else if seenOptional then
      vs := vs ++ [s!"required param `{p.name}` follows a defaulted param"]
  -- 3+4: content-slot placement, and no event param after it
  let mut lastContent : Option Nat := none
  let mut lastRequired : Option Nat := none
  let mut firstOptional : Option Nat := none
  for i in [0:ps.size] do
    let p := ps[i]!
    if isContentLike p then lastContent := some i
    if p.optional then firstOptional := firstOptional <|> some i
    else lastRequired := some i
  if let some c := lastContent then
    unless lastRequired == some c || firstOptional == some c do
      vs := vs ++ [s!"content slot `{ps[c]!.name}` is unreachable by a trailing `do` " ++
        "(must be the last required or the first defaulted param)"]
    for i in [c+1:ps.size] do
      if isEventLike ps[i]! then
        vs := vs ++ [s!"event param `{ps[i]!.name}` after the content slot"]
  -- 5: event params named `on…`
  for p in ps do
    if isEventLike p && !p.name.toString.startsWith "on" then
      vs := vs ++ [s!"event param `{p.name}` should be named `on…`"]
  return vs

/-- Rule 7 for one declaration (already known to return `Composable α`,
`α ≠ Unit`). -/
def valueNamingViolations (declName : Name) : List String :=
  let s := lastComponent declName
  if s.isEmpty || s.front.isLower then []
  else [s!"returns a value (`Composable α`, `α ≠ Unit`) — name it lowerCamelCase"]

/-! ## Fixtures

Deliberately nonconforming private decls; the command asserts each trips its
rule (and that a conforming one is clean) before scanning the real library.
They live in this test module, outside the scanned `Compose.*` prefixes. -/

private def GoodComponent (onClick : IO Unit) (content : Composable Unit)
    (modifier : Compose.Modifier := {}) (enabled : Bool := true) : Composable Unit :=
  fun _ => do let _ := (onClick, modifier, enabled); content.run ‹_›

private def BadNoModifier (content : Composable Unit) : Composable Unit := content

private def BadModifierNoDefault (content : Composable Unit)
    (modifier : Compose.Modifier) : Composable Unit :=
  fun c => do let _ := modifier; content.run c

private def BadParamOrder (enabled : Bool := true) (onClick : IO Unit)
    (modifier : Compose.Modifier := {}) : Composable Unit :=
  fun _ => do let _ := (enabled, onClick, modifier); pure ()

private def BadContentPlacement (content : Composable Unit) (onClick : IO Unit)
    (modifier : Compose.Modifier := {}) : Composable Unit :=
  fun c => do let _ := (onClick, modifier); content.run c

private def BadEventAfterContent (label : String) (content : Composable Unit := pure ())
    (onHover : IO Unit := pure ()) (modifier : Compose.Modifier := {}) : Composable Unit :=
  fun c => do let _ := (label, onHover, modifier); content.run c

private def BadEventName (click : IO Unit) (content : Composable Unit)
    (modifier : Compose.Modifier := {}) : Composable Unit :=
  fun c => do let _ := (click, modifier); content.run c

private def BadValueComposable : Composable Nat := pure 7

/-- The fixture expectations: decl ↦ substring that must appear in its
violations (`none` = must be clean). -/
def fixtureExpectations : List (Name × Option String) :=
  [(``GoodComponent, none),
   (``BadNoModifier, some "missing a `modifier"),
   (``BadModifierNoDefault, some "no `:= {}` default"),
   (``BadParamOrder, some "follows a defaulted param"),
   (``BadContentPlacement, some "unreachable by a trailing"),
   (``BadEventAfterContent, some "after the content slot"),
   (``BadEventName, some "should be named `on…`")]

/-- Does `s` contain `sub`? (Substring search via `splitOn`.) -/
def containsSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Source location of a declaration, for error messages. -/
def locationOf (declName : Name) : CoreM String := do
  let env ← getEnv
  let mod := env.getModuleIdxFor? declName |>.bind
    (fun i => env.header.moduleNames[i.toNat]?)
  let path := match mod with
    | some m => "/".intercalate (m.components.map toString) ++ ".lean"
    | none => "<current file>"
  match ← findDeclarationRanges? declName with
  | some rs => return s!"{path}:{rs.range.pos.line}"
  | none => return path

elab "#composeApiLint" "(" "minComponents" ":=" minN:num ")" : command => do
  liftTermElabM do
    let defaultMod ← Term.elabTermEnsuringType (← `(({} : Compose.Modifier)))
      (mkConst ``Compose.Modifier)
    Term.synthesizeSyntheticMVarsNoPostponing
    -- Self-test on the fixtures before trusting the scan.
    for (n, expected?) in fixtureExpectations do
      let vs ← componentViolations defaultMod n
      match expected? with
      | none =>
        unless vs.isEmpty do
          throwError "ApiLint self-test: {n} should be clean, got: {vs}"
      | some sub =>
        unless vs.any (containsSub · sub) do
          throwError "ApiLint self-test: {n} should trip \"{sub}\", got: {vs}"
    unless (valueNamingViolations ``BadValueComposable).length == 1 do
      throwError "ApiLint self-test: BadValueComposable should trip the naming rule"
    -- Scan the built Compose modules.
    let env ← getEnv
    let mut components := 0
    let mut failed := false
    for h : i in [0:env.header.moduleNames.size] do
      let mod := env.header.moduleNames[i]
      unless (`Compose).isPrefixOf mod do continue
      let isComponentModule := componentPrefixes.any (·.isPrefixOf mod)
      for declName in env.header.moduleData[i]!.constNames do
        if declName.isInternalDetail then continue
        let some ci := env.find? declName | continue
        let report (vs : List String) : TermElabM Unit := do
          unless vs.isEmpty do
            logError m!"#composeApiLint: {declName} ({← locationOf declName}):{
              vs.foldl (fun a v => a ++ "\n  • " ++ v) ""}"
        -- Rule 6: CompositionLocal constants are Local*.
        if let .app (.const ``Compose.CompositionLocal _) _ := ci.type.cleanupAnnotations then
          unless (lastComponent declName).startsWith "Local" do
            report ["`CompositionLocal` constants must be named `Local…`"]
            failed := true
        let cod := (codomainOf ci.type).cleanupAnnotations
        -- Rule 7: value-returning composables are lowerCamelCase.
        if isComposableValue cod then
          let vs := valueNamingViolations declName
          report vs
          failed := failed || !vs.isEmpty
        -- Rules 1-5: uppercase Composable-Unit components in the widget modules.
        if isComponentModule && isComposableUnit cod
            && (lastComponent declName).front.isUpper then
          components := components + 1
          let vs ← componentViolations defaultMod declName
          report vs
          failed := failed || !vs.isEmpty
    if components < minN.getNat then
      throwError "#composeApiLint: scanned only {components} components (< {minN.getNat}) — \
        the module filter is likely stale"
    unless failed do
      trace[Elab.info] "#composeApiLint: {components} components clean"

#composeApiLint (minComponents := 30)

/-! ## StateInit gate pins (Part A of the compose-rules adoption)

Negative: binding a state builder directly in composition must not compile.
Positive: the `remember` idioms and the plain-`IO` constructors must. These
anchor the gate against toolchain changes in coercion/lift resolution. -/

section GatePins
open Compose

#guard_msgs (drop info) in
#check_failure (do
  let s ← mutableStateOf true
  s.set false : Composable Unit)

#guard_msgs (drop info) in
#check_failure (do
  let _ ← derivedStateOf (pure (0 : Nat))
  pure () : Composable Unit)

-- `remember` takes the builders directly…
example : Composable Unit := do
  let s ← remember (mutableStateOf true)
  s.set false
example : Composable Unit := do
  let s ← rememberKeyed "k" (mutableStateOf (0 : Nat))
  let _ ← s.get
  pure ()
-- …generic `IO` initializers lift in…
example : Composable Unit := do
  let r ← remember (IO.mkRef (0 : Nat))
  let _ ← r.get
  pure ()
example : Composable Unit := do
  let x ← remember (pure "v")
  let _ := x
  pure ()
example : Composable Unit := do
  let x ← remember do
    let r ← IO.mkRef (3 : Nat)
    r.get
  let _ := x
  pure ()
-- …initializers compose in the `StateInit` monad…
example (xs : Array Nat) : Composable Unit := do
  let _ ← remember (xs.mapM fun x => mutableStateOf x)
  pure ()
-- …and plain `IO` uses the `create` constructors (or `.run`).
example : IO Unit := do
  let s ← MutableState.create true
  s.set false
example : IO (MutableState Bool) := (mutableStateOf true).run

end GatePins

end Tests.ApiLint
