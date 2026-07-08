import Compose.Ui.Input.HitTest

namespace Compose

/-!
# Hover and cursor shapes (`Compose/Ui/Input/Hover.lean`)

Hover-path diffing: on every (uncaptured) pointer move the tree is hit-tested
and the new path compared with the previous one by node identity — nodes that
left receive an `exit` pointer event (leaf→root), nodes that entered an
`enter` event (root→leaf), so nested hover states behave (hovering a child
keeps the parent hovered). Mirrors the enter/exit synthesis of Compose's
`PointerInputEventProcessor`.

The cursor: after each diff, the leaf-most `Modifier.pointerHoverIcon` on the
hovered path wins (`topmost hovered wins`); no icon restores the default.
Setting goes through the injectable `CursorSetter` — the real SDL setter
caches created system cursors and swallows errors (dummy driver), tests
inject a recorder.
-/

/-- Injectable cursor sink. `set` is called only on actual changes. -/
structure CursorSetter where
  set : Sdl.SystemCursor → IO Unit

/-- The real SDL setter: creates each `SystemCursor` once (cached), then
`Sdl.setCursor`s it. Failures (headless dummy driver, exotic platforms) are
swallowed — a cursor is cosmetic. -/
def CursorSetter.sdl : IO CursorSetter := do
  let cache ← IO.mkRef (#[] : Array (Sdl.SystemCursor × Sdl.Cursor))
  return { set := fun sc => do
    try
      let cursor ← do
        match (← cache.get).find? (·.1 == sc) with
        | some (_, c) => pure c
        | none =>
          let c ← Sdl.createSystemCursor sc
          cache.modify (·.push (sc, c))
          pure c
      Sdl.setCursor cursor
    catch _ => pure () }

/-- Per-window hover state: the hovered hit path and the cursor plumbing. -/
structure HoverState where
  /-- Hovered path as of the last move (root→leaf). -/
  path : IO.Ref (Array HitTarget)
  cursor : CursorSetter
  /-- Last cursor set, to skip redundant `set` calls. -/
  currentCursor : IO.Ref Sdl.SystemCursor

namespace HoverState

/-- Fresh state (nothing hovered, default cursor assumed). -/
def create (cursor : CursorSetter) : IO HoverState :=
  return { path := ← IO.mkRef #[], cursor, currentCursor := ← IO.mkRef .default }

/-- The leaf-most `pointerHoverIcon` among the path's hit elements, else
`default`. -/
private def resolveCursor (path : Array HitTarget) : IO Sdl.SystemCursor := do
  for i in [0:path.size] do
    let t := path[path.size - 1 - i]!
    let elems := (← t.node.data).modifier.elems
    for j in [0:t.elems.size] do
      if let some (.pointer (.hoverIcon c)) := elems[t.elems[t.elems.size - 1 - j]!]? then
        return c
  return .default

/-- Diff the hovered path against a fresh hit test at `pos` (`none` = pointer
left the window): deliver `exit` to departed nodes (leaf→root) and `enter` to
new ones (root→leaf), update the cursor (topmost `pointerHoverIcon` wins,
default restored), and return the new path (the caller usually dispatches the
`move` along it). `base` supplies the mods/timestamp for the synthesized
events. -/
def update (hs : HoverState) (root : LayoutNode) (base : PointerEvent)
    (pos : Option Offset) : IO (Array HitTarget) := do
  let oldPath ← hs.path.get
  let newPath ← match pos with
    | some p => root.hitTest p
    | none => pure #[]
  let oldIds ← oldPath.mapM (·.node.nodeId)
  let newIds ← newPath.mapM (·.node.nodeId)
  -- Exits leaf→root.
  for i in [0:oldPath.size] do
    let j := oldPath.size - 1 - i
    unless newIds.contains oldIds[j]! do
      oldPath[j]!.deliver { base with eventType := .exit } base.position
  -- Enters root→leaf.
  for i in [0:newPath.size] do
    unless oldIds.contains newIds[i]! do
      newPath[i]!.deliver { base with eventType := .enter } base.position
  hs.path.set newPath
  let want ← resolveCursor newPath
  unless (← hs.currentCursor.get) == want do
    hs.currentCursor.set want
    hs.cursor.set want
  return newPath

end HoverState

end Compose
