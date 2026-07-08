/-!
# Minimal runtime test harness

Mirrors lean-sdl3's harness shape: `check`/`checkEq`/`checkThrows` report one
line per assertion and bump a global failure counter; `group` runs a module's
tests, turning an unexpected throw into a failure instead of aborting the run;
`summary` returns the process exit code (1 if anything failed).
`COMPOSE_TEST_GROUP=<Name>` runs a single group.
-/

namespace Tests.Harness

/-- Global failure counter. -/
initialize failures : IO.Ref Nat ← IO.mkRef 0

/-- Record a pass/fail for a boolean condition. -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"ok {name}"
  else
    IO.eprintln s!"FAIL {name}"
    failures.modify (· + 1)

/-- Record a pass/fail for an equality, printing both sides on mismatch. -/
def checkEq [BEq α] [ToString α] (name : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    IO.println s!"ok {name}"
  else
    IO.eprintln s!"FAIL {name}: got {actual}, want {expected}"
    failures.modify (· + 1)

/-- Passes iff `act` throws an `IO` error. -/
def checkThrows {α : Type} (name : String) (act : IO α) : IO Unit := do
  let threw ← try
      let _ ← act
      pure false
    catch _ =>
      pure true
  check name threw

/-- Run one module's tests; an unexpected throw is a failure, not an abort.
When `COMPOSE_TEST_GROUP` is set, groups with a different name are skipped. -/
def group (name : String) (body : IO Unit) : IO Unit := do
  if let some only ← IO.getEnv "COMPOSE_TEST_GROUP" then
    if only != name then
      return
  IO.println s!"-- {name} --"
  try
    body
  catch e =>
    IO.eprintln s!"FAIL {name} raised: {e}"
    failures.modify (· + 1)

/-- Final tally; exit code 1 iff any check failed. -/
def summary : IO UInt32 := do
  let n ← failures.get
  if n == 0 then
    IO.println "\nAll tests passed."
    return 0
  else
    IO.eprintln s!"\n{n} test(s) FAILED."
    return 1

end Tests.Harness
