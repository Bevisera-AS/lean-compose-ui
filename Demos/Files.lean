import Compose

/-!
# File manager demo (`lake exe demo-files`)

A minimal but working file browser: a **breadcrumb** of clickable path segments
for navigating up and down, a **listing** of the current directory (directories
first, then files, each group case-insensitively sorted) rendered with a
virtualized `LazyColumn` + `VerticalScrollbar`, and an **info panel** that shows
a clicked file's name, full path, size (exact bytes + human-readable), and
modified time.

It only opens directories: clicking a directory row navigates into it, clicking
a file row selects it and fills the info panel — no file is ever read. The app
starts at `$HOME` (falling back to `/`). Dotfiles are hidden by default; the
header's **"Show hidden" switch** reveals them (turning it off drops a selected
dotfile from the info panel too).

## Pure, testable core

Everything that is not IO or drawing is a pure function with inline `#guard`s:

* `breadcrumbs` — a path string → the clickable `(label, targetPath)` segments;
* `childPath` — a directory + child name → the child's path;
* `sortEntries` / `entryLt` — the dirs-first, case-insensitive ordering;
* `humanSize` — bytes → `"1.4 MB"`-style text (binary units, 1 KB = 1024 B);
* `formatEpoch` — epoch seconds → `"YYYY-MM-DD HH:MM:SS UTC"`.

## Injected filesystem (`FsSource`)

Filesystem access is a single injected function

```
FsSource := String → IO (Except String (Array FsEntry))
```

mirroring how `Demos/Gallery.lean` injects `launch`: the production app passes
`realFs` (`System.FilePath.readDir` + per-entry `.metadata`), while the MT suite
(`test/ComposeTests/Files.lean`) passes a fake in-memory tree — so the tests
touch no real filesystem. An unreadable directory yields `Except.error`, which
the UI shows as an inline error state while keeping the breadcrumb live, so the
user can always navigate away. Broken symlinks / stat failures degrade to a
plain file entry rather than crashing.

Long breadcrumb paths **scroll horizontally** rather than wrapping.

Headless: `SDL_VIDEO_DRIVER=dummy COMPOSE_MAX_FRAMES=60 lake exe demo-files`.
-/

namespace Demos.Files
open Compose

/-! ## Pure model -/

/-- One listing entry: a name, whether it is a directory, its byte size (`none`
when unknown, e.g. a directory or an un-stattable entry), and its modification
time in whole epoch seconds (`none` when unavailable). -/
structure FsEntry where
  /-- The bare file name (no directory part). -/
  name : String
  /-- Whether the entry is a directory (following symlinks). -/
  isDir : Bool
  /-- Size in bytes, if known (files only). -/
  size : Option UInt64 := none
  /-- Modification time in whole seconds since the Unix epoch, if known. -/
  modified : Option Int := none
  deriving BEq, Repr, Inhabited

/-- A directory reader: a path → its entries, or an error message (e.g.
permission denied). Injected so tests drive a fake tree (see the module
docstring). Mirrors the `launch` injection in `Demos/Gallery.lean`. -/
abbrev FsSource := String → IO (Except String (Array FsEntry))

/-! ### Breadcrumb segments -/

/-- The clickable breadcrumb segments for an absolute path: the root `("/", "/")`
followed by one `(label, targetPath)` per component, where clicking `label`
navigates to `targetPath`. Repeated/trailing slashes collapse. -/
def breadcrumbs (path : String) : Array (String × String) := Id.run do
  let comps := (path.splitOn "/").filter (· != "")
  let mut acc := #[("/", "/")]
  let mut cur := ""
  for c in comps do
    cur := cur ++ "/" ++ c
    acc := acc.push (c, cur)
  return acc

#guard breadcrumbs "/" == #[("/", "/")]
#guard breadcrumbs "" == #[("/", "/")]
#guard breadcrumbs "/Users/pcn" ==
  #[("/", "/"), ("Users", "/Users"), ("pcn", "/Users/pcn")]
#guard breadcrumbs "/Users/pcn/Projects" ==
  #[("/", "/"), ("Users", "/Users"), ("pcn", "/Users/pcn"), ("Projects", "/Users/pcn/Projects")]
#guard breadcrumbs "/a//b/" == #[("/", "/"), ("a", "/a"), ("b", "/a/b")]  -- collapses slashes

/-- The path of `name` inside directory `dir` (root-aware, so `/` + `x` is
`/x`, not `//x`). -/
def childPath (dir name : String) : String :=
  if dir == "/" then "/" ++ name else dir ++ "/" ++ name

#guard childPath "/" "Users" == "/Users"
#guard childPath "/Users/pcn" "Projects" == "/Users/pcn/Projects"

/-! ### Sorting: directories first, then case-insensitive alphabetical -/

/-- Strict `<` on strings (Bool), via the core `Ord String`. -/
private def strLt (a b : String) : Bool := compare a b == .lt

/-- The listing order: directories before files, and within each group by
case-insensitive name. -/
def entryLt (a b : FsEntry) : Bool :=
  if a.isDir == b.isDir then strLt a.name.toLower b.name.toLower
  else a.isDir

/-- Sort entries directories-first, then case-insensitively by name. -/
def sortEntries (es : Array FsEntry) : Array FsEntry := es.qsort entryLt

private def sortSample : Array FsEntry :=
  #[{ name := "banana.txt", isDir := false, size := some 10 },
    { name := "Apple", isDir := true },
    { name := "apple.txt", isDir := false, size := some 5 },
    { name := "zebra", isDir := true }]

#guard (sortEntries sortSample).map (·.name) == #["Apple", "zebra", "apple.txt", "banana.txt"]
#guard (sortEntries #[]).isEmpty
-- Case-insensitive within a group (dotfiles sort normally).
#guard (sortEntries #[{ name := "b", isDir := false }, { name := ".A", isDir := false },
    { name := "a", isDir := false }]).map (·.name) == #[".A", "a", "b"]

/-! ### Hidden-file filtering -/

/-- Dotfile convention: a name starting with `.` is hidden. -/
def isHidden (name : String) : Bool := name.startsWith "."

/-- The entries to list: everything when `showHidden`, otherwise dotfiles are
dropped. -/
def visibleEntries (showHidden : Bool) (es : Array FsEntry) : Array FsEntry :=
  if showHidden then es else es.filter (fun e => !isHidden e.name)

#guard visibleEntries true (sortSample.push { name := ".git", isDir := true }) ==
  sortSample.push { name := ".git", isDir := true }
#guard (visibleEntries false #[{ name := ".git", isDir := true },
    { name := "a", isDir := false }, { name := ".x", isDir := false }]).map (·.name) == #["a"]
#guard (visibleEntries false #[]).isEmpty

/-! ### Human-readable sizes -/

/-- A byte count as human-readable text: `"{n} B"` under 1 KB, otherwise one
decimal place in binary KB/MB/GB/TB/PB (1 KB = 1024 B). -/
def humanSize (bytes : Nat) : String := Id.run do
  if bytes < 1024 then return s!"{bytes} B"
  let units := #["KB", "MB", "GB", "TB", "PB"]
  let mut div := 1024
  let mut unit := 0
  while bytes ≥ div * 1024 && unit + 1 < units.size do
    div := div * 1024
    unit := unit + 1
  let tenths := bytes * 10 / div
  return s!"{tenths / 10}.{tenths % 10} {units[unit]!}"

#guard humanSize 0 == "0 B"
#guard humanSize 1023 == "1023 B"
#guard humanSize 1024 == "1.0 KB"
#guard humanSize 1536 == "1.5 KB"
#guard humanSize (1024 * 1024) == "1.0 MB"
#guard humanSize 1468007 == "1.4 MB"      -- 1468007 / 1048576 = 1.400… → 1.4 MB
#guard humanSize 1468006 == "1.3 MB"      -- one byte under the 1.4 boundary truncates
#guard humanSize (1024 * 1024 * 1024) == "1.0 GB"
#guard humanSize (1024 * 1024 * 1024 * 1024) == "1.0 TB"

/-! ### Epoch-seconds formatting -/

/-- Zero-pad a small nonnegative integer to two digits. -/
private def pad2 (n : Int) : String :=
  let s := toString n
  if s.length < 2 then "0" ++ s else s

/-- `(year, month, day)` for a day count since 1970-01-01, via Howard Hinnant's
`civil_from_days` (truncation-toward-zero division matches Lean's `Int` `/`). -/
private def civilFromDays (z0 : Int) : Int × Int × Int :=
  let z := z0 + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- Epoch seconds → `"YYYY-MM-DD HH:MM:SS UTC"` (plain UTC, no locale). -/
def formatEpoch (sec : Int) : String :=
  let days := sec / 86400
  let sod := sec % 86400
  let (y, m, d) := civilFromDays days
  s!"{y}-{pad2 m}-{pad2 d} {pad2 (sod / 3600)}:{pad2 (sod % 3600 / 60)}:{pad2 (sod % 60)} UTC"

#guard formatEpoch 0 == "1970-01-01 00:00:00 UTC"
#guard formatEpoch 86461 == "1970-01-02 00:01:01 UTC"
#guard formatEpoch 1704067200 == "2024-01-01 00:00:00 UTC"
#guard formatEpoch 1700000000 == "2023-11-14 22:13:20 UTC"

/-! ## Real filesystem source -/

/-- The production `FsSource`: read the directory and stat each entry. A failed
directory read (e.g. permission denied) becomes `Except.error`; a per-entry
stat failure (broken symlink, special file) degrades to a plain file entry so a
listing never crashes. `metadata` follows symlinks, so a symlink to a directory
lists as a directory (navigable) and a symlink to a file as a file (selectable);
neither is ever opened. -/
def realFs : FsSource := fun path => do
  try
    let entries ← (System.FilePath.mk path).readDir
    let mut out := #[]
    for e in entries do
      let info ← try
          let md ← e.path.metadata
          pure { name := e.fileName, isDir := md.type == .dir,
                 size := some md.byteSize, modified := some md.modified.sec : FsEntry }
        catch _ =>
          pure { name := e.fileName, isDir := false : FsEntry }
      out := out.push info
    return .ok out
  catch err =>
    return .error (toString err)

/-! ## UI state + navigation -/

/-- The browser's mutable state: the current directory, its listing (or an error
message), and the currently selected file (for the info panel). -/
structure FilesState where
  /-- The current directory path. -/
  cwd : MutableState String
  /-- The current listing, or an error message for an unreadable directory. -/
  listing : MutableState (Except String (Array FsEntry))
  /-- The selected file entry, if any. -/
  selected : MutableState (Option FsEntry)
  /-- Whether dotfiles are listed (the header switch; off by default). -/
  showHidden : MutableState Bool
  /-- Whether a directory read is currently in flight (the async listing gap). -/
  loading : MutableState Bool
  /-- Monotonic id bumped by every `navigate`; a completed read only writes the
  listing when it still matches, dropping results a newer navigation raced past. -/
  generation : IO.Ref Nat

/-- Flip the hidden-files switch. Turning it off also drops a selected dotfile
(its row just disappeared; the info panel must not describe an invisible
entry). -/
def FilesState.setShowHidden (st : FilesState) (b : Bool) : IO Unit := do
  st.showHidden.set b
  unless b do
    if let some e ← st.selected.get then
      if isHidden e.name then st.selected.set none

/-- Navigate to `path`. The path and selection update **synchronously** (so the
breadcrumb responds to a click at once), then the directory is read **off the UI
thread** (`IO.asTask`) and its listing delivered back on the main loop through
`scope` — a blocking or network-mounted read never freezes the UI. A per-request
generation guard drops a result a newer navigation has superseded, so rapid
navigation never lands a stale directory; the previous listing stays visible
(`loading` flags the gap) until the new one arrives. -/
def navigate (scope : LaunchScope) (fs : FsSource) (st : FilesState)
    (path : String) : IO Unit := do
  st.cwd.set path
  st.selected.set none
  st.loading.set true
  let gen ← st.generation.modifyGet (fun g => (g + 1, g + 1))
  -- A dedicated thread: a directory read is blocking IO and must not occupy a
  -- shared compute-pool worker (that starves other work / can deadlock a small
  -- pool when several reads are in flight).
  let task ← IO.asTask (fs path) (prio := .dedicated)
  let _ ← scope.launch do
    let outcome ← UiTask.await task
    -- Only the latest request may write the listing (stale-result guard).
    if (← st.generation.get) == gen then
      st.listing.set (match outcome with
        | .ok r => r
        | .error e => .error (toString e))
      st.loading.set false

/-- Fresh, unloaded state pointing at `home`; the first composition of
`filesBody` kicks off the initial (async) listing load. Used by the tests. -/
def FilesState.init (home : String) : IO FilesState := do
  let st : FilesState :=
    { cwd := ← mutableStateOf home,
      -- `Except` has no `BEq`, and every navigation genuinely re-reads, so
      -- always-notify is both required and correct here.
      listing := ← mutableStateOfAlwaysNotify (.ok #[]),
      selected := ← mutableStateOf none,
      showHidden := ← mutableStateOf false,
      loading := ← mutableStateOf false,
      generation := ← IO.mkRef 0 }
  return st

/-! ## Composables -/

/-- The breadcrumb strip: the path's segments, `›`-separated, each a clickable
target. Horizontally scrollable so a long path never breaks the layout. -/
composable def breadcrumbBar (scope : LaunchScope) (fs : FsSource) (st : FilesState) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let path ← st.cwd.get
  let scroll ← rememberScrollState
  Row (modifier := (Modifier.testTag "breadcrumb" |>.fillMaxWidth).horizontalScroll scroll
        |>.padding (horizontal := some 12) (vertical := some 8))
      (verticalAlignment := .centerVertically) do
    let segs := breadcrumbs path
    for h : i in [0:segs.size] do
      let (label, target) := segs[i]
      if i > 0 then
        Text " › " (color := some colors.onSurfaceVariant)
      Text label (modifier := Modifier.testTag s!"crumb:{target}"
            |>.clickable (navigate scope fs st target)
            |>.padding (horizontal := some 4) (vertical := some 2))
        (color := some colors.primary)

/-- One listing row: a drawn folder/file glyph, the name, and (for files) a
human-readable size. Clicking a directory navigates in; clicking a file selects
it. Highlighted when selected. -/
composable def fileRow (scope : LaunchScope) (fs : FsSource) (st : FilesState)
    (e : FsEntry) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  -- Read the selection *here* so this row's own restart scope tracks it: a
  -- `LazyColumn` item skips while its index is unchanged, so only a per-row
  -- read makes the highlight follow the selection (Compose's stable-lambda
  -- skip means a value threaded from the parent would never update). Compare by
  -- the stable identity (name + kind — the row's key) so a reused row resolves.
  let isSelected := match ← st.selected.get with
    | some s => s.name == e.name && s.isDir == e.isDir
    | none => false
  -- The tap coroutine is retained across keyed row reuse (its key is constant),
  -- so the click must read the *live* directory and entry rather than values
  -- captured at composition — `st` is a stable handle and (name, kind) is the
  -- row's key, so both stay correct even when the node is recycled.
  let onClick : IO Unit := do
    if e.isDir then
      navigate scope fs st (childPath (← st.cwd.get) e.name)
    else
      match ← st.listing.get with
      | .ok entries =>
        match entries.find? (fun x => x.name == e.name && x.isDir == e.isDir) with
        | some cur => st.selected.set (some cur)
        | none => pure ()
      | .error _ => pure ()
  Row (modifier := Modifier.testTag s!"row:{e.name}"
        |>.semantics (selected := some isSelected)
        |>.clickable onClick
        |>.fillMaxWidth
        |>.background (if isSelected then colors.primaryContainer else colors.surface)
        |>.padding (horizontal := some 12) (vertical := some 6))
      (verticalAlignment := .centerVertically)
      (horizontalArrangement := .spacedBy 10) do
    -- A simple drawn glyph: a filled square (accent for dirs, muted for files).
    Box (modifier := Modifier.width 14 |>.height 14
          |>.background (if e.isDir then colors.primary else colors.outline)
            (shape := .rounded 3))
    Text (if e.isDir then e.name ++ "/" else e.name) (modifier := Modifier.weight 1)
    match e.size with
    | some n => Text (humanSize n.toNat) (color := some colors.onSurfaceVariant)
    | none => pure ()

/-- The info panel (bottom strip): the selected file's name, full path, exact +
human size, and modified time; a hint when nothing is selected. -/
composable def infoPanel (st : FilesState) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let cwd ← st.cwd.get
  Surface (modifier := Modifier.testTag "info" |>.fillMaxWidth) (color := colors.surfaceVariant) do
    Column (modifier := Modifier.padding (all := 12)) (verticalArrangement := .spacedBy 2) do
      match ← st.selected.get with
      | none =>
        Text "Select a file to see its details." (color := some colors.onSurfaceVariant)
      | some e => do
        Text e.name (style := { fontSize := 15, weight := .bold })
        Text (childPath cwd e.name) (color := some colors.onSurfaceVariant)
        match e.size with
        | some n => Text s!"{n} bytes ({humanSize n.toNat})"
        | none => Text "size: unknown"
        match e.modified with
        | some sec => Text s!"modified: {formatEpoch sec}"
        | none => pure ()

/-- The listing area: the sorted rows in a virtualized `LazyColumn` with a
`VerticalScrollbar`, or an inline error / empty state. -/
composable def listingArea (scope : LaunchScope) (fs : FsSource) (st : FilesState) :
    Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  let showHidden ← st.showHidden.get
  let scroll ← rememberScrollState
  Box (modifier := Modifier.fillMaxWidth |>.fillMaxHeight |>.background colors.surface) do
    match ← st.listing.get with
    | .error msg =>
      Box (modifier := Modifier.testTag "error" |>.fillMaxSize |>.padding (all := 16))
        (contentAlignment := .topStart)
        (Text s!"Cannot open this folder: {msg}" (color := some colors.error))
    | .ok entries =>
      let sorted := sortEntries (visibleEntries showHidden entries)
      if sorted.isEmpty then
        Box (modifier := Modifier.fillMaxSize |>.padding (all := 16))
          (Text "(empty folder)" (color := some colors.onSurfaceVariant))
      else do
        -- Key rows by entry identity (name + kind), not index: a `LazyColumn`
        -- item skips recomposition while its *index* is unchanged, so a plain
        -- index key would show stale rows after navigating to a different
        -- directory whose entry at that index differs.
        LazyColumn scroll (itemHeight := 28) (count := sorted.size)
          (key := fun i => mixKeys (stringKey sorted[i]!.name)
            (if sorted[i]!.isDir then 1 else 0))
          (modifier := Modifier.fillMaxSize)
          fun i => fileRow scope fs st sorted[i]!
        VerticalScrollbar scroll (Modifier.align .topEnd |>.fillMaxHeight)
    -- A subtle in-flight hint, shown over the (still-visible) previous listing.
    if ← st.loading.get then
      Text "Loading…" (modifier := Modifier.testTag "loading"
          |>.align .bottomStart |>.padding (all := 8))
        (color := some colors.onSurfaceVariant)

/-- The header's hidden-files toggle: a labeled `Switch` (a standalone,
immediate-effect option — Material's switch case, not a checkbox's). -/
composable def showHiddenToggle (st : FilesState) : Composable Unit := do
  let colors ← MaterialTheme.colorScheme
  Row (modifier := Modifier.padding (horizontal := some 12))
      (verticalAlignment := .centerVertically) (horizontalArrangement := .spacedBy 6) do
    Text "Show hidden" (style := { fontSize := 13 })
      (color := some colors.onSurfaceVariant)
    Switch (← st.showHidden.get) st.setShowHidden
      (modifier := Modifier.testTag "show-hidden")

/-- The whole browser: header (breadcrumb + hidden-files switch), listing, and
info panel. Factored on the injected `FsSource` + `FilesState` so the MT suite
drives it over a fake tree. -/
composable def filesBody (fs : FsSource) (st : FilesState) : Composable Unit := do
  -- A launch scope tied to the whole screen (not a row): in-flight loads must
  -- survive the row recycling that navigation triggers.
  let scope ← rememberLaunchScope
  -- Kick off the initial listing load exactly once (async, like every other
  -- navigation), so a slow home directory never blocks first composition.
  let _ ← remember (do navigate scope fs st (← st.cwd.get); pure true)
  Column (modifier := Modifier.fillMaxSize) do
    Row (modifier := Modifier.fillMaxWidth) (verticalAlignment := .centerVertically) do
      Box (modifier := Modifier.weight 1) (breadcrumbBar scope fs st)
      showHiddenToggle st
    Box (modifier := Modifier.weight 1 |>.fillMaxWidth) (listingArea scope fs st)
    infoPanel st

/-- The file-manager screen: remembers the state and mounts `filesBody` (which
kicks off the initial `home` load). `home` is `$HOME` in production; a fake root
in tests. -/
composable def filesUi (fs : FsSource) (home : String) : Composable Unit := do
  let cwd ← remember (mutableStateOf home)
  let listing ← remember (mutableStateOfAlwaysNotify (.ok #[] : Except String (Array FsEntry)))
  let selected ← remember (mutableStateOf (none : Option FsEntry))
  let showHidden ← remember (mutableStateOf false)
  let loading ← remember (mutableStateOf false)
  let generation ← remember (IO.mkRef 0)
  let st : FilesState := { cwd, listing, selected, showHidden, loading, generation }
  MaterialTheme (filesBody fs st)

/-- The real app: browse the actual filesystem starting at `$HOME` (or `/`). -/
def filesApp : Composable Unit := do
  let home := (← IO.getEnv "HOME").getD "/"
  filesUi realFs home

end Demos.Files
