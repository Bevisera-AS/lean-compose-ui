module

public import Compose.Ui.Input.HitTest
public meta import Compose.Ui.Input.HitTest

public section

namespace Compose

/-!
# Bring into view (`Compose/Ui/Input/BringIntoView.lean`)

The dispatcher half of bring-into-view: a node's reveal request walks its
ancestor chain outward and asks every scroll container's
`FocusElem.bringIntoView` responder (attached by
`Modifier.verticalScroll`/`horizontalScroll`) to scroll the minimal amount
that makes the node visible. There is no registry — the modifier chain
*is* the node→scroll-state link, resolved on demand, correct across
re-parenting, and naturally scoped to overlay subtrees.

Requests are raised by focus gains and IME inset changes
(`WindowContext.requestBringIntoView`) and serviced by `renderFrame`
right after remeasure, when positions are final — that ordering makes an
IME-raised request see the post-`imePadding` layout instead of racing it.
Mirrors `BringIntoViewRequester` resolving against scrollable responders.
-/

namespace LayoutNode

/-- Ask every ancestor scroll container to reveal this node: the node's
root-coordinate bounds walk the parent chain outward; each responder
receives them localized to its viewport wrapper (the resolved region of
the `bringIntoView` element — exactly the clipped viewport box) and
returns the shift its content is about to make, pre-compensating what the
rest of the walk sees, plus an animation the dispatcher launches. All
animations run concurrently (Compose semantics), each interruptible
through its own scroll state's mutation generation. Responders whose
wrapper region is not yet resolved (fresh, unmeasured nodes) are
skipped. -/
partial def bringIntoView (n : LayoutNode) (sched : Scheduler) : IO Unit := do
  let d ← n.data
  go d.parent (Rect.ofOffsetSize (← n.originInRoot) d.size.toSize)
where
  go : Option LayoutNode → Rect → IO Unit
    | none, _ => pure ()
    | some p, rect0 => do
      let d ← p.data
      let mut rect := rect0
      -- Innermost element first: an inner responder reveals within its own
      -- viewport before an outer one sees the (shifted) bounds.
      for i in [0:d.modifier.elems.size] do
        let idx := d.modifier.elems.size - 1 - i
        if let some (.focus (.bringIntoView _ r)) := d.modifier.elems[idx]? then
          if let some rd := d.resolvedDraws.find? (·.elemIdx == idx) then
            let vpOrigin := (← p.originInRoot) + rd.offset.toOffset
            let (shift, task?) ← r.respond (rect.translate (-vpOrigin)) rd.size.toSize
            rect := rect.translate shift
            if let some t := task? then
              let _ ← sched.launch t
      go d.parent rect

end LayoutNode

end Compose

end
