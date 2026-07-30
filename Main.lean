import Demos.Gallery

/-!
# Gallery launcher entry point (`lake exe gallery`)

A thin `main` over `Demos.Gallery`. `--list` prints one registered demo exe
name per line (machine-readable; `scripts/smoke-demos.sh` discovers demos
this way). A bare run opens the interactive launcher window
(`Demos.Gallery.galleryUi`): each row's **Launch** button spawns that demo's
executable via `spawnDemo`.
-/

open Compose Demos.Gallery

/-- The registered demo exe names, in launcher order (the `--list` payload).
Derived from the gallery registry so the two never drift. -/
def demos : List String := Demos.Gallery.demos.map (·.exe)

/-- Spawn a demo executable as a detached child process: prefer the built
binary (`.lake/build/bin/<exe>`), falling back to `lake exe <exe>` when it
is absent (e.g. an unbuilt demo). The gallery keeps running. -/
def spawnDemo (exe : String) : IO Unit := do
  let bin := s!".lake/build/bin/{exe}"
  let spec : IO.Process.SpawnArgs :=
    if ← System.FilePath.pathExists bin then { cmd := bin }
    else { cmd := "lake", args := #["exe", exe] }
  try
    let _ ← IO.Process.spawn spec
  catch e =>
    IO.eprintln s!"gallery: failed to launch {exe}: {e}"

/-- Entry point: `--list` prints the demo exe names; otherwise open the
launcher window. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--list" then
    demos.forM IO.println
    return 0
  runMaterialApp "compose-ui demos" 520 560 (galleryUi spawnDemo)
