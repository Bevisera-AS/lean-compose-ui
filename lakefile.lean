import Lake
open Lake DSL System

/-!
# compose-ui build

A Lean lakefile (rather than TOML) because our executables link the SDL3 system
libraries transitively (via `Compose/Ui/Draw/Scope.lean`), and the link flags
must be *discovered* at build time — pkg-config → Homebrew → standard prefixes —
so binaries build on macOS and Linux CI alike. The `sdl` dependency's own
`moreLinkArgs` are not propagated to a downstream package's executables, so we
replicate the discovery here.
-/

/-- Run a process, returning trimmed stdout on success; `none` if it fails or
the executable is missing. -/
def tryCmd (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none
  catch _ => return none

/-- Locate one library's dir by probing Homebrew and standard prefixes for the
actual shared library. `none` = hope the default linker path has it. -/
def findLibDir (brewPkg stem : String) : IO (Option String) := do
  let candidates ← do
    let mut cs := #[]
    if let some p ← tryCmd "brew" #["--prefix", brewPkg] then
      cs := cs.push p
    pure (cs ++ #["/opt/homebrew", "/usr/local", "/usr"])
  for p in candidates do
    for ext in ["dylib", "so", "so.0"] do
      if ← (FilePath.mk p / "lib" / s!"{stem}.{ext}").pathExists then
        return some s!"{p}/lib"
  return none

/-- SDL3 link flags: pkg-config → Homebrew/standard prefixes → bare `-lSDL3
-lSDL3_ttf`. `-Wl,-rpath` entries let the binaries run without
`DYLD_LIBRARY_PATH`/`LD_LIBRARY_PATH`. Mirrors the `sdl` dependency's discovery. -/
def findLinkArgs : IO (Array String) := do
  if let some libs ← tryCmd "pkg-config" #["--libs", "sdl3", "sdl3-ttf"] then
    let args := libs.splitOn " " |>.filter (· ≠ "") |>.toArray
    let rpaths := args.filterMap fun a =>
      if a.startsWith "-L" then some s!"-Wl,-rpath,{a.drop 2}" else none
    return args ++ rpaths
  let sdlDir ← findLibDir "sdl3" "libSDL3"
  let ttfDir ← findLibDir "sdl3_ttf" "libSDL3_ttf"
  let dirs := ([sdlDir, ttfDir].filterMap id).eraseDups.toArray
  return (dirs.map (s!"-L{·}")) ++ #["-lSDL3", "-lSDL3_ttf"]
      ++ (dirs.map (s!"-Wl,-rpath,{·}"))

-- `moreLinkArgs` is a pure package field; run the discovery once via the
-- standard implemented_by/opaque bridge.
unsafe def sdlLinkArgsImpl : Array String :=
  unsafeBaseIO do
    match ← findLinkArgs.toBaseIO with
    | .ok args => pure args
    | .error _ => pure #["-lSDL3", "-lSDL3_ttf"]

@[implemented_by sdlLinkArgsImpl]
opaque sdlLinkArgs : Array String

package «compose-ui» where
  moreLinkArgs := sdlLinkArgs

require sdl from git
  "https://github.com/philnguyen/lean-sdl3" @ "e5dc25504402b87fbc9368ac366922fd8e66974c"

@[default_target]
lean_lib Compose

/-- Demo gallery launcher (individual 7GUIs demos get their own exes as they
land); `--list` prints the registered demo exe names. -/
lean_exe gallery where
  root := `Main

/-- M5 smoke demo: timers + frame clock + recomposition + remeasure
(`Demos/Smoke.lean`). -/
lean_exe «demo-smoke» where
  root := `Demos.Smoke

/-- M9 widget gallery: every Material widget, interactive, light + dark
(`Demos/Widgets.lean`). -/
lean_exe «demo-widgets» where
  root := `Demos.Widgets

/-- Registers the `ComposeTests.*` submodules (Harness + per-milestone groups)
so the test exe can import them; a bare `lean_exe` does not glob its srcDir.
(Named `ComposeTests` because the sdl dependency already exports `Tests.*`
modules, and Lake module names are workspace-global.) -/
lean_lib ComposeTests where
  srcDir := "test"
  globs := #[.andSubmodules `ComposeTests]

/-- Headless test runner: `SDL_VIDEO_DRIVER=dummy SDL_AUDIO_DRIVER=dummy lake
exe test` (`COMPOSE_TEST_GROUP=<Name>` runs one group). -/
@[test_driver]
lean_exe test where
  srcDir := "test"
  root := `ComposeTests
