module

public import Compose.Material.Icon
public meta import Compose.Material.Icon

public section

namespace Compose.Material.Icons

/-!
# Built-in icons

A small set of Material Design icons as `IconVector`s (24-unit viewport,
classic filled style), enough for app chrome: navigation, dialogs, media,
settings, charts. Grow the set by pasting Material Symbols path data into
`IconVector.ofPathData` — the paired `#guard` rejects a bad paste at
compile time.
-/

open Compose (IconVector)

/-- One compile-time sanity check per icon: the path parsed non-empty. -/
private def ok (i : IconVector) : Bool := i.path.verbs.size > 0

/-- C-style back arrow. Material `arrow_back`. -/
def arrowBack : IconVector := .ofPathData "arrowBack"
  "M20 11H7.83l5.59-5.59L12 4l-8 8 8 8 1.41-1.41L7.83 13H20v-2z"
#guard ok arrowBack

/-- Close ("X"). Material `close`. -/
def close : IconVector := .ofPathData "close"
  "M19 6.41L17.59 5 12 10.59 6.41 5 5 6.41 10.59 12 5 17.59 6.41 19 12 13.41 17.59 19 19 17.59 13.41 12z"
#guard ok close

/-- Checkmark. Material `check`. -/
def check : IconVector := .ofPathData "check"
  "M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"
#guard ok check

/-- Plus. Material `add`. -/
def add : IconVector := .ofPathData "add"
  "M19 13h-6v6h-2v-6H5v-2h6V5h2v6h6v2z"
#guard ok add

/-- Minus. Material `remove`. -/
def remove : IconVector := .ofPathData "remove"
  "M19 13H5v-2h14v2z"
#guard ok remove

/-- Play triangle. Material `play_arrow`. -/
def playArrow : IconVector := .ofPathData "playArrow"
  "M8 5v14l11-7z"
#guard ok playArrow

/-- Pause bars. Material `pause`. -/
def pause : IconVector := .ofPathData "pause"
  "M6 19h4V5H6v14zm8-14v14h4V5h-4z"
#guard ok pause

/-- Circular refresh arrow. Material `refresh`. -/
def refresh : IconVector := .ofPathData "refresh"
  "M17.65 6.35C16.2 4.9 14.21 4 12 4c-4.42 0-7.99 3.58-7.99 8s3.57 8 7.99 8c3.73 0 6.84-2.55 7.73-6h-2.08c-.82 2.33-3.04 4-5.65 4-3.31 0-6-2.69-6-6s2.69-6 6-6c1.66 0 3.14.69 4.22 1.78L13 11h7V4l-2.35 2.35z"
#guard ok refresh

/-- Settings gear. Material `settings`. -/
def settings : IconVector := .ofPathData "settings"
  "M19.14 12.94c.04-.3.06-.61.06-.94 0-.32-.02-.64-.07-.94l2.03-1.58c.18-.14.23-.41.12-.61l-1.92-3.32c-.12-.22-.37-.29-.59-.22l-2.39.96c-.5-.38-1.03-.7-1.62-.94l-.36-2.54c-.04-.24-.24-.41-.48-.41h-3.84c-.24 0-.43.17-.47.41l-.36 2.54c-.59.24-1.13.57-1.62.94l-2.39-.96c-.22-.08-.47 0-.59.22L2.74 8.87c-.12.21-.08.47.12.61l2.03 1.58c-.05.3-.09.63-.09.94s.02.64.07.94l-2.03 1.58c-.18.14-.23.41-.12.61l1.92 3.32c.12.22.37.29.59.22l2.39-.96c.5.38 1.03.7 1.62.94l.36 2.54c.05.24.24.41.48.41h3.84c.24 0 .44-.17.47-.41l.36-2.54c.59-.24 1.13-.56 1.62-.94l2.39.96c.22.08.47 0 .59-.22l1.92-3.32c.12-.22.07-.47-.12-.61l-2.01-1.58zM12 15.6c-1.98 0-3.6-1.62-3.6-3.6s1.62-3.6 3.6-3.6 3.6 1.62 3.6 3.6-1.62 3.6-3.6 3.6z"
#guard ok settings

/-- Bar chart. Material `bar_chart`. -/
def barChart : IconVector := .ofPathData "barChart"
  "M5 9.2h3V19H5V9.2zm5.6-4.2h2.8v14h-2.8V5zm5.6 8H19v6h-2.8v-6z"
#guard ok barChart

/-- Volume/speaker. Material `volume_up`. -/
def volumeUp : IconVector := .ofPathData "volumeUp"
  "M3 9v6h4l5 5V4L7 9H3zm13.5 3c0-1.77-1.02-3.29-2.5-4.03v8.05c1.48-.73 2.5-2.25 2.5-4.02zM14 3.23v2.06c2.89.86 5 3.54 5 6.71s-2.11 5.85-5 6.71v2.06c4.01-.91 7-4.49 7-8.77s-2.99-7.86-7-8.77z"
#guard ok volumeUp

end Compose.Material.Icons

end
