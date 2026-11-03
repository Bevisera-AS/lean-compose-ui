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
    let base ← match ← findLinkArgs.toBaseIO with
      | .ok args => pure args
      | .error _ => pure #["-lSDL3", "-lSDL3_ttf"]
    -- On Linux, an SDL3 built from source links against the host glibc and so
    -- references symbol versions (e.g. `pthread_join@GLIBC_2.34`) newer than
    -- the ones in the Lean toolchain's bundled sysroot. Lean links executables
    -- with `--no-allow-shlib-undefined`, which then rejects those undefined
    -- symbols in `libSDL3.so` even though the runtime loader resolves them
    -- against the system libc. Re-allow shared-lib undefineds on Linux only
    -- (macOS's ld64 neither needs nor understands this flag).
    if System.Platform.isOSX || System.Platform.isWindows then
      pure base
    else
      pure (base.push "-Wl,--allow-shlib-undefined")

@[implemented_by sdlLinkArgsImpl]
opaque sdlLinkArgs : Array String

package «compose-ui» where
  moreLinkArgs := sdlLinkArgs

-- For day-to-day cross-repo work against a sibling checkout, override with
-- an untracked .lake/package-overrides.json instead of editing this.
require sdl from "../lean-sdl3"

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

/-- Wave-2 Liquid Glass showcase: `Theme.liquidGlass` over a vivid backdrop —
glass toolbar/panel, seam-driven glass card, frosted dialog
(`Demos/Glass.lean`). -/
lean_exe «demo-glass» where
  root := `Demos.Glass

/-- M10 overlay gallery: LazyColumn + scrollbar, dropdown menu, alert dialog
(`Demos/Overlays.lean`). -/
lean_exe «demo-overlays» where
  root := `Demos.Overlays

-- M12 7GUIs demos. Each demo's screen + pure logic live in a `main`-free
-- library module (`Demos/<X>.lean`) so its MT test suite can import it; the
-- `main` entry point is a thin shim (`Demos/<X>Main.lean`, the exe root),
-- because Lean forbids two `main`s in one import closure.

/-- M12 7GUIs Counter: read-only field + increment button (`Demos/Counter.lean`). -/
lean_exe «demo-counter» where
  root := `Demos.CounterMain

/-- M12 7GUIs Temperature Converter: bidirectionally synced C/F fields
(`Demos/TempConverter.lean`). -/
lean_exe «demo-tempconv» where
  root := `Demos.TempConverterMain

/-- M12 7GUIs Flight Booker: mode combobox + validated date fields + dialog
(`Demos/FlightBooker.lean`). -/
lean_exe «demo-flight» where
  root := `Demos.FlightBookerMain

/-- M12 7GUIs Timer: gauge + duration slider + reset, ticking off the frame
clock. Model + UI live in `Demos/Timer.lean` (importable by the MT suite); the
`_root_.main` entry is in `Demos/TimerApp.lean` (see that module's note). -/
lean_exe «demo-timer» where
  root := `Demos.TimerApp

/-- M12 7GUIs CRUD: prefix-filtered listbox + name/surname fields +
create/update/delete. Model + UI live in `Demos/Crud.lean` (importable by the
MT suite); the `_root_.main` entry is in `Demos/CrudApp.lean`. -/
lean_exe «demo-crud» where
  root := `Demos.CrudApp

/-- M12: the CircleDrawer model + composable UI (`Demos/CircleDrawer/Model.lean`),
its own lib so both the `demo-circles` exe and the MT test group can import it.
A `Demos/CircleDrawer/**` submodule belongs to no other lib, and the exe root
(`Demos/CircleDrawer.lean`) only adds `_root_.main` — which the test must not
import twice. Purely additive. -/
lean_lib CircleDrawerModel where
  srcDir := "."
  globs := #[.submodules `Demos.CircleDrawer]

/-- M12: the 7GUIs CircleDrawer demo — undo/redo over a circle canvas, with a
right-click popup menu and a live diameter-adjust dialog
(`Demos/CircleDrawer.lean`). -/
lean_exe «demo-circles» where
  root := `Demos.CircleDrawer

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

/-- M13: the Cells modules (`Demos/Cells/*`): the pure, SDL-free formula
engine (`Engine.lean`, imports only `Std`) and — since M13b — the demo UI on
top of it (`Ui.lean`, imports `Compose`). Declared as a `default_target` lib
so `lake build` compiles both (running the engine's `#guard`s) and so the
`ComposeTests` lib can import `Demos.Cells.Ui` for the MT behavior suite. -/
@[default_target]
lean_lib CellsEngine where
  srcDir := "."
  globs := #[.submodules `Demos.Cells]

/-- M13b: the Cells demo — a 2-axis virtualized spreadsheet with sticky
headers over the pure engine (`Demos/Cells/Ui.lean`; the root is a separate
module so the UI stays importable by the test lib without a `main` clash). -/
lean_exe «demo-cells» where
  root := `Demos.CellsMain

/-- M15 desktop-components showcase: multi-window `application`, in-window
`MenuBar`, `ContextMenuArea`, `Tooltip`s, an About `DialogWindow`, and a
`Tray`. Model + UI live in `Demos/Desktop.lean` (importable by the MT suite);
the `_root_.main` entry is in `Demos/DesktopMain.lean`. -/
lean_exe «demo-desktop» where
  root := `Demos.DesktopMain

/-- Final demo: a minimal file manager — breadcrumb navigation, dirs-first
sorted listing (`LazyColumn` + scrollbar), and a file info panel over an
injected `FsSource`. Model + UI live in `Demos/Files.lean` (importable by the MT
suite); the `_root_.main` entry is in `Demos/FilesMain.lean`. -/
lean_exe «demo-files» where
  root := `Demos.FilesMain

/-- M-b GPU spike: probes the SDL_GPU runtime facts the GPU renderer backend
depends on (MSL-source shaders, firstInstance, `gpuDrawData` conventions,
transfer-buffer cycle, present loop). Real driver only — SDL_GPU has no
dummy-video backend — so it is not in the headless suite; run
`lake exe gpu-probe` locally (`Demos/GpuProbe.lean`). -/
lean_exe «gpu-probe» where
  root := `Demos.GpuProbeMain

/-- M-d parity diff: renders identical display lists through the GPU renderer
(offscreen) and the software SDL backend and asserts per-scene pixel-difference
bounds. Real driver only; `scripts/smoke-gpu.sh` runs it (`Demos/GpuParity.lean`). -/
lean_exe «gpu-parity» where
  root := `Demos.GpuParityMain

/-- The GPU probe/parity *bodies* as an importable lib (no `_root_.main` —
the exe shims are `Demos.GpuProbeMain`/`Demos.GpuParityMain`), so downstream
packages can wrap them: LeAndroid ships `Demos.GpuProbe.run` as an on-device
APK. Not a default target — real drivers only. -/
lean_lib GpuChecks where
  srcDir := "."
  globs := #[.one `Demos.GpuProbe, .one `Demos.GpuParity]

/-- M12 demo *libraries* (model + UI, no `_root_.main`): the reusable modules
the demo exes wrap and the MT suites import. Declared as their own
`default_target` lib (like `CellsEngine`) so `lake build` compiles them, runs
their `#guard`s, and propagates the sdl dependency's native code for
interpretation. The `_root_.main` entry points live in the sibling
`Demos.<X>Main`/`Demos.<X>App` shim modules (the exe roots) — kept separate
because two `_root_.main`-defining modules cannot both be imported by the
single test runner. -/
@[default_target]
lean_lib Demos where
  srcDir := "."
  globs := #[.one `Demos.Counter, .one `Demos.TempConverter,
    .one `Demos.FlightBooker, .one `Demos.Timer, .one `Demos.Crud,
    .one `Demos.Desktop, .one `Demos.Files, .one `Demos.Gallery]
