import Compose
import ComposeTests.Harness
import Demos.Files

/-!
# File manager demo behavior tests (`test/ComposeTests/Files.lean`)

The file-manager demo (`Demos/Files.lean`) exercised two ways:

* **Pure core** — `checkEq`s for `breadcrumbs`, `childPath`, `sortEntries`,
  `humanSize`, and `formatEpoch` (the compile-time `#guard`s next to the
  definitions cover the same ground; these keep the runtime counter honest).
* **MT scenarios** over a **fake in-memory tree** injected as the `FsSource`
  (no real filesystem is touched): the initial listing is dirs-first sorted;
  clicking a directory navigates in (breadcrumb grows, listing changes);
  clicking a breadcrumb segment navigates back up; clicking a file fills the
  info panel; and a permission-denied directory shows the error state while the
  breadcrumb still recovers.
-/

namespace Tests.Files
open Compose Compose.Test Tests.Harness Demos.Files

/-! ## Fake filesystem -/

private def dir (name : String) : FsEntry := { name, isDir := true }
private def file (name : String) (size : UInt64) (mod : Option Int := none) : FsEntry :=
  { name, isDir := false, size := some size, modified := mod }

/-- A tiny in-memory tree rooted at `/home/user`, with one permission-denied
directory (`/home/user/secret`). Any unknown path is an empty directory. -/
private def fakeFs : FsSource := fun path =>
  return match path with
  | "/" => .ok #[dir "home"]
  | "/home" => .ok #[dir "user"]
  | "/home/user" => .ok #[
      -- Deliberately unsorted, mixed case, with a dotfile, to prove the sort.
      file "readme.md" 100,
      dir "Pictures",
      file "notes.txt" 2048 (some 1704067200),   -- 2.0 KB, 2024-01-01 00:00:00 UTC
      dir "secret",
      dir "Documents",
      file ".hidden" 42]
  | "/home/user/Documents" => .ok #[file "report.pdf" 1500000, file "a.txt" 10]
  | "/home/user/secret" => .error "permission denied"
  | _ => .ok #[]

/-- Fresh demo state navigated to the fake home. -/
private def fresh : IO FilesState := FilesState.init fakeFs "/home/user"

/-! ## Pure core -/

private def pureCore : IO Unit := do
  -- Breadcrumb segments and their navigation targets.
  checkEq "breadcrumbs root" (breadcrumbs "/") #[("/", "/")]
  checkEq "breadcrumbs nested" (breadcrumbs "/home/user")
    #[("/", "/"), ("home", "/home"), ("user", "/home/user")]
  checkEq "childPath from root" (childPath "/" "home") "/home"
  checkEq "childPath nested" (childPath "/home/user" "Documents") "/home/user/Documents"
  -- Dirs-first, case-insensitive sort (dotfiles included).
  checkEq "sort dirs-first, case-insensitive"
    ((sortEntries #[file "readme.md" 1, dir "Pictures", dir "Documents",
        file ".x" 1, file "apple" 1]).map (·.name))
    #["Documents", "Pictures", ".x", "apple", "readme.md"]
  -- Human-readable sizes across the unit boundaries.
  checkEq "size 0 B" (humanSize 0) "0 B"
  checkEq "size 1023 B" (humanSize 1023) "1023 B"
  checkEq "size 1.0 KB" (humanSize 1024) "1.0 KB"
  checkEq "size 2.0 KB" (humanSize 2048) "2.0 KB"
  checkEq "size 1.0 MB" (humanSize (1024 * 1024)) "1.0 MB"
  checkEq "size 1.0 GB" (humanSize (1024 * 1024 * 1024)) "1.0 GB"
  -- Epoch formatting.
  checkEq "epoch 0" (formatEpoch 0) "1970-01-01 00:00:00 UTC"
  checkEq "epoch 2024" (formatEpoch 1704067200) "2024-01-01 00:00:00 UTC"

/-! ## Initial listing is dirs-first sorted -/

private def initialListing : IO Unit := do
  let st ← fresh
  runComposeTest (content := filesBody fakeFs st) (width := 640) (height := 480) do
    -- Directories (shown with a trailing slash) and files are all present.
    assertExists (.tag "row:Documents")
    assertExists (.tag "row:Pictures")
    assertExists (.tag "row:secret")
    assertExists (.tag "row:notes.txt")
    assertExists (.tag "row:readme.md")
    assertExists (.tag "row:.hidden")           -- dotfiles are shown
    assertExists (.text "Documents/")           -- directory glyph text
    -- The breadcrumb starts at the fake home.
    assertExists (.tag "crumb:/")
    assertExists (.tag "crumb:/home")
    assertExists (.tag "crumb:/home/user")
    -- The model's sorted view is dirs-first, then case-insensitive.
    let lst ← st.listing.get
    match lst with
    | .ok es =>
      checkEq "initial sort order" ((sortEntries es).map (·.name))
        #["Documents", "Pictures", "secret", ".hidden", "notes.txt", "readme.md"]
    | .error e =>
      check s!"unexpected error listing: {e}" false

/-! ## Clicking a directory navigates into it -/

private def enterDirectory : IO Unit := do
  let st ← fresh
  runComposeTest (content := filesBody fakeFs st) (width := 640) (height := 480) do
    click (.tag "row:Documents")
    checkEq "cwd moved into Documents" (← st.cwd.get) "/home/user/Documents"
    -- The listing changed to the subdirectory's contents.
    assertExists (.tag "row:report.pdf")
    assertExists (.tag "row:a.txt")
    assertMissing (.tag "row:notes.txt")
    -- The breadcrumb grew a segment for the new directory.
    assertExists (.tag "crumb:/home/user/Documents")

/-! ## Clicking a breadcrumb segment navigates back up -/

private def breadcrumbUp : IO Unit := do
  let st ← fresh
  runComposeTest (content := filesBody fakeFs st) (width := 640) (height := 480) do
    click (.tag "row:Documents")
    checkEq "descended into Documents" (← st.cwd.get) "/home/user/Documents"
    -- Click the "user" breadcrumb segment to go back up.
    click (.tag "crumb:/home/user")
    checkEq "breadcrumb navigated back up" (← st.cwd.get) "/home/user"
    assertExists (.tag "row:notes.txt")
    assertMissing (.tag "row:report.pdf")
    -- Going all the way to root works too.
    click (.tag "crumb:/")
    checkEq "breadcrumb navigated to root" (← st.cwd.get) "/"
    assertExists (.tag "row:home")

/-! ## Clicking a file shows its info -/

private def fileInfo : IO Unit := do
  let st ← fresh
  runComposeTest (content := filesBody fakeFs st) (width := 640) (height := 480) do
    -- Nothing selected initially → the hint is shown.
    assertExists (.text "Select a file to see its details.")
    click (.tag "row:notes.txt")
    check "file selected in model"
      ((← st.selected.get) == some (file "notes.txt" 2048 (some 1704067200)))
    -- The info panel shows name, full path, formatted size, and modified time.
    assertExists (.text "notes.txt")
    assertExists (.text "/home/user/notes.txt")
    assertExists (.text "2048 bytes (2.0 KB)")
    assertExists (.text "modified: 2024-01-01 00:00:00 UTC")
    -- Clicking a directory row does not select a file (it navigates instead).
    click (.tag "row:Documents")
    check "selection cleared on navigation" ((← st.selected.get) == none)

/-! ## A permission-denied directory shows the error state; breadcrumb recovers -/

private def permissionDenied : IO Unit := do
  let st ← fresh
  runComposeTest (content := filesBody fakeFs st) (width := 640) (height := 480) do
    click (.tag "row:secret")
    checkEq "cwd moved into secret" (← st.cwd.get) "/home/user/secret"
    -- The listing is the inline error state, not a crash.
    assertExists (.tag "error")
    assertExists (Matcher.textContains "permission denied")
    assertMissing (.tag "row:notes.txt")
    -- The breadcrumb still works, so the user can escape.
    assertExists (.tag "crumb:/home/user")
    click (.tag "crumb:/home/user")
    checkEq "recovered from the error via breadcrumb" (← st.cwd.get) "/home/user"
    assertMissing (.tag "error")
    assertExists (.tag "row:notes.txt")

/-- The Files group. -/
def run : IO Unit := do
  scenario "pureCore" pureCore
  scenario "initialListing" initialListing
  scenario "enterDirectory" enterDirectory
  scenario "breadcrumbUp" breadcrumbUp
  scenario "fileInfo" fileInfo
  scenario "permissionDenied" permissionDenied

end Tests.Files
