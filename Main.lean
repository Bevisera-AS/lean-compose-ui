import Compose

/-- Registered demo executables (`lake exe <name>`); grows as demos land.
The interactive gallery UI is M14 — for now this is the launcher's registry,
consumed by `scripts/smoke-demos.sh` via `--list`. -/
def demos : List String := ["demo-smoke", "demo-widgets", "demo-overlays"]

/-- Demo gallery entry point: `--list` prints one registered demo exe name
per line (machine-readable); a bare run prints them with a usage hint. -/
def main (args : List String) : IO Unit := do
  if args.contains "--list" then
    demos.forM IO.println
  else
    IO.println "compose-ui demos — run one with: lake exe <name>"
    demos.forM (fun d => IO.println s!"  {d}")
