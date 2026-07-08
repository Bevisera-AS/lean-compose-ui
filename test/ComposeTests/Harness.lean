import Sdl

/-!
# Minimal runtime test harness

Mirrors lean-sdl3's harness shape: `check`/`checkEq`/`checkThrows` report one
line per assertion and bump a global failure counter; `group` runs a module's
tests, turning an unexpected throw into a failure instead of aborting the run;
`summary` returns the process exit code (1 if anything failed).
`COMPOSE_TEST_GROUP=<Name>` runs a single group. Pixel-probe helpers
(`colorNear`, `showColor`) for readback assertions live here too.
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

/-- Run one MT-framework scenario (a `Compose.Test.runComposeTest` call):
its assertions print their own `ok` lines and *throw* on failure, so a throw
here is counted as one failure and later scenarios in the group still run. -/
def scenario (name : String) (body : IO Unit) : IO Unit := do
  try
    body
  catch e =>
    IO.eprintln s!"FAIL {name}: {e}"
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

/-- Absolute difference of two `Nat`s. -/
private def natDist (a b : Nat) : Nat := max a b - min a b

/-- Whether SDL pixel `c` is within `tol` byte-steps of `(r, g, b)` per RGB
channel (alpha ignored). -/
def colorNear (c : Sdl.Color) (r g b : UInt8) (tol : Nat := 2) : Bool :=
  natDist c.r.toNat r.toNat <= tol && natDist c.g.toNat g.toNat <= tol &&
  natDist c.b.toNat b.toNat <= tol

/-- Human-readable rendering of an SDL pixel, for failure diagnostics. -/
def showColor (c : Sdl.Color) : String := s!"({c.r},{c.g},{c.b},{c.a})"

end Tests.Harness
