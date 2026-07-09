import Compose.Ui.Modifier
import Compose.Runtime.State
import Compose.Runtime.Applier

namespace Compose

/-!
# LayoutNode (`Compose/Ui/Node.lean`)

The mutable node of the layout tree, mirroring
`androidx.compose.ui.node.LayoutNode`. A node is a single `IO.Ref` to a
`LayoutNodeData` record, boxed through `SlotVal` to tie the recursive knot
(the same audited pattern as `Compose.Runtime.Composer`'s `Group`; the box
invariantly holds an `IO.Ref LayoutNodeData`).

**Measurement** folds the modifier chain (outermost first) into a wrapper
chain around the node's inner measurable, old-Compose `LayoutNodeWrapper`
style: each layout element transforms constraints downward and
size/placement upward; each draw element is *resolved* — its offset within
the node's outer box and the size of the wrapper it decorates are recorded —
for the draw walk in `Compose.Ui.Layout`.

**Dirty tracking** mirrors DESIGN.md's simplified `requestRemeasure`:
invalidating a node sets its `needsRemeasure` and flags every ancestor with
`needsRelayout`. The next root pass descends through `needsRelayout` nodes
re-measuring dirty descendants *in place* (with their cached constraints);
only if a descendant's size actually changes does the ancestor re-run its own
measure policy — i.e. propagation stops at the first node whose cached size
survives. Measurement short-circuits entirely when the constraints are
unchanged and no dirty flag is set. State reads inside measure policies and
placement blocks are observed (M1 observer stack) and invalidate exactly the
reading node. A mark raised *during* a pass (a state write inside a measure
block) is never lost: `measureIn` clears `needsRelayout` only when no child
is left dirty — the mark's path stays connected to the root — and `remeasure`
reports residual dirt through the owner hook, scheduling the follow-up frame
that settles it.

**Reference cycles**: parent and child hold strong references to each other,
which Lean's RC does not collect. Nodes live for the composition's lifetime;
on applier `remove`, every parent link in the removed subtree is severed so
the subtree becomes acyclic and frees once the composition drops it.

This module calls no SDL API; `Sdl` is only a transitive import via
`Modifier.drawBehind`'s `DrawM` payload.
-/

/-- Move `count` elements of `xs` from `src` to `dst` (both indices in the
pre-move list) — Compose's `AbstractApplier.move` convention. -/
private def moveRange (xs : Array α) (src dst count : Nat) : Array α :=
  if src == dst || count == 0 then xs else
    let dest := if src > dst then dst else dst - count
    let block := xs.extract src (src + count)
    let rest := xs.extract 0 src ++ xs.extract (src + count) xs.size
    rest.extract 0 dest ++ block ++ rest.extract dest rest.size

#guard moveRange #[1, 2, 3, 4, 5] 2 0 2 == #[3, 4, 1, 2, 5]
#guard moveRange #[1, 2, 3, 4, 5] 0 3 1 == #[2, 3, 1, 4, 5]
#guard moveRange #[1, 2, 3, 4, 5] 1 1 2 == #[1, 2, 3, 4, 5]

/-- Remove `count` elements of `xs` starting at `idx`. -/
private def removeRange (xs : Array α) (idx count : Nat) : Array α :=
  xs.extract 0 idx ++ xs.extract (idx + count) xs.size

#guard removeRange #[1, 2, 3, 4] 1 2 == #[1, 4]
#guard removeRange #[1, 2, 3] 0 3 == (#[] : Array Nat)

/-- A node of the layout tree (see the module docstring). Mirrors
`androidx.compose.ui.node.LayoutNode`. -/
structure LayoutNode where
  /-- Invariantly an `IO.Ref LayoutNodeData` (ties the recursive knot). -/
  box : SlotVal
  deriving Inhabited

/-- A non-layout (draw/pointer/focus) modifier element resolved during
measurement: which chain element it is, at what offset within the node's
outer box, and the size of the wrapper it decorates. The draw walk executes
the draw entries; the hit-test walk (`Compose.Ui.Input.HitTest`) tests the
pointer/focus entries and applies `clip` entries geometrically. -/
structure ResolvedDraw where
  /-- Index into the node's `modifier.elems`. -/
  elemIdx : Nat
  /-- Top-left of the decorated wrapper, relative to the node's outer box. -/
  offset : IntOffset
  /-- Size of the decorated wrapper. -/
  size : IntSize
  deriving Repr, BEq, Inhabited

/-- One entry of a node's tessellation cache: the mesh a `background`/`border`
draw element last tessellated, with the `Draw.MeshKey` it was built from. The
draw walk (`LayoutNode.cachedMesh`) reuses the mesh while the key — the fully
resolved tessellation inputs — is unchanged, so static shapes are not
re-triangulated on every rendered frame. Compose analog: `Modifier.background`
and `Modifier.border` caching their `Outline`/`Path` in `drawWithCache` until
size or shape changes. -/
structure MeshCacheEntry where
  /-- Index into the node's `modifier.elems` (same convention as
  `ResolvedDraw.elemIdx`). -/
  elemIdx : Nat
  /-- The tessellation inputs `mesh` was built from (validity check). -/
  key : Draw.MeshKey
  /-- The cached mesh, in the wrapper's local coordinates. -/
  mesh : Draw.Mesh
  deriving Inhabited

/-- The mutable payload of one `LayoutNode`. -/
structure LayoutNodeData where
  parent : Option LayoutNode := none
  children : Array LayoutNode := #[]
  modifier : Modifier := {}
  policy : MeasurePolicy := .root
  /-- Identity of the policy's inputs when the caller can provide one; `none`
  means the policy is treated as changed on every update (Compose's
  capturing-lambda behavior). -/
  policyInputs : Option UInt64 := none
  /-- Density for `Dp` resolution, pushed down from the root measure pass. -/
  density : Density := {}
  /-- Measured outer size (after all modifiers). -/
  size : IntSize := .zero
  /-- Constraints of the last completed measure (cache key). -/
  lastConstraints : Option Constraints := none
  /-- Position within the parent's content coordinate space (set by the
  parent's placement block). -/
  position : IntOffset := .zero
  /-- Offset from the node's outer box to its content coordinate space
  (accumulated placement of the layout wrappers: padding, offset, …). -/
  contentOffset : IntOffset := .zero
  /-- Non-layout modifiers resolved by the last measure (see `ResolvedDraw`). -/
  resolvedDraws : Array ResolvedDraw := #[]
  /-- Cached tessellated meshes of the chain's `background`/`border` elements,
  keyed by chain index (see `MeshCacheEntry`; maintained by
  `LayoutNode.cachedMesh`). -/
  meshCache : Array MeshCacheEntry := #[]
  /-- Runtime state of the chain's `pointerInput` elements, ordinally aligned
  with them. Reconciled by `LayoutNode.reconcilePointerInputs` (called from
  `Layout`'s update phase); coroutines are cancelled when the node leaves the
  tree (`severParentLinks`, the detach hook). -/
  pointerInputs : Array PointerInputState := #[]
  /-- The node's own measurement is invalid. -/
  needsRemeasure : Bool := true
  /-- Some descendant needs remeasuring; the next pass descends through here.
  -/
  needsRelayout : Bool := false
  /-- Owner hook, set on the *root* node by the app shell: called whenever a
  dirty walk reaches this parentless node, i.e. whenever any node in the tree
  newly needs remeasuring. Mirrors `LayoutNode.owner?.onRequestMeasure`
  scheduling a frame. -/
  onRequestRemeasure : Option (IO Unit) := none
  /-- Two-way registration on the states read by measure/placement. -/
  registry : ObservationRegistry

instance : Nonempty LayoutNodeData :=
  ⟨{ registry := { dep := ⟨0, pure ()⟩, reads := Classical.choice inferInstance } }⟩

namespace LayoutNode

/-- The underlying mutable cell. -/
def cell (n : LayoutNode) : IO.Ref LayoutNodeData := n.box.get!

/-- Read the node's data. -/
def data (n : LayoutNode) : IO LayoutNodeData := n.cell.get

/-- Mutate the node's data. -/
def modifyData (n : LayoutNode) (f : LayoutNodeData → LayoutNodeData) : IO Unit :=
  n.cell.modify f

/-- The measured outer size. -/
def size (n : LayoutNode) : IO IntSize := return (← n.data).size

/-- The position within the parent's content coordinate space. -/
def position (n : LayoutNode) : IO IntOffset := return (← n.data).position

/-- Offset from the outer box to the content coordinate space. -/
def contentOffset (n : LayoutNode) : IO IntOffset := return (← n.data).contentOffset

/-- The `i`-th child (throws when out of bounds). -/
def child (n : LayoutNode) (i : Nat) : IO LayoutNode := do
  let d ← n.data
  if h : i < d.children.size then
    return d.children[i]
  else
    throw <| IO.userError s!"LayoutNode.child: index {i} out of bounds ({d.children.size})"

/-- Flag every ancestor with `needsRelayout` so the next root pass descends
to this node; stops at an ancestor already on a dirty path — that ancestor's
own dirtying already notified the owner, or (mid-pass) the pass keeps the
flag and `remeasure` notifies at the end. At the parentless top, fires the
`onRequestRemeasure` owner hook. The upward half of Compose's
`requestRemeasure` propagation. -/
partial def markAncestorsNeedRelayout (n : LayoutNode) : IO Unit := do
  let d ← n.data
  match d.parent with
  | none => if let some notify := d.onRequestRemeasure then notify
  | some p =>
    let pd ← p.data
    if pd.needsRelayout || pd.needsRemeasure then return
    p.modifyData fun dd => { dd with needsRelayout := true }
    p.markAncestorsNeedRelayout

/-- Invalidate the node's measurement (state write in a measure lambda,
modifier/policy change, child list change) and make it reachable by the next
root pass. Mirrors `LayoutNode.requestRemeasure`. -/
def markNeedsRemeasure (n : LayoutNode) : IO Unit := do
  n.modifyData fun d => { d with needsRemeasure := true }
  n.markAncestorsNeedRelayout

/-- Allocate a detached node with default (root-like) policy; its measure
observation registry is wired to `markNeedsRemeasure`. -/
def create : IO LayoutNode := do
  let invalidateRef ← IO.mkRef (pure () : IO Unit)
  let registry ← ObservationRegistry.create
    { id := ← freshId, invalidate := do (← invalidateRef.get) }
  let ref ← IO.mkRef ({ registry } : LayoutNodeData)
  let n : LayoutNode := ⟨SlotVal.mk ref⟩
  invalidateRef.set n.markNeedsRemeasure
  return n

/-- Install the owner hook on a root node: `notify` runs whenever a dirty
walk reaches this node from anywhere in its tree (see
`LayoutNodeData.onRequestRemeasure`). -/
def setOnRequestRemeasure (n : LayoutNode) (notify : IO Unit) : IO Unit :=
  n.modifyData fun d => { d with onRequestRemeasure := some notify }

/-- Set the node's position (from a parent placement block). -/
def setPosition (n : LayoutNode) (pos : IntOffset) : IO Unit :=
  n.modifyData fun d => { d with position := pos }

/-- Process-unique identity of the node (hover-path diffing and focus
tracking compare by it; `LayoutNode` has no useful `BEq`). -/
def nodeId (n : LayoutNode) : IO Nat :=
  return (← n.data).registry.dep.id

/-- Sever every parent link inside the subtree, making it acyclic so RC can
free it once the composition drops its references (see the module docstring
on cycles). Doubles as the subtree's *detach* hook: every `pointerInput`
coroutine in it is cancelled — the applier calls this on `remove` and on
composition clear, so handlers stop when their node leaves the composition
(the input analog of `LaunchedEffect`'s cancel-on-forget). -/
partial def severParentLinks (n : LayoutNode) : IO Unit := do
  (← n.data).pointerInputs.forM (·.cancel)
  n.modifyData fun d => { d with parent := none, pointerInputs := #[] }
  (← n.data).children.forM severParentLinks

/-- The `Applier` over layout nodes (erase with `Applier.erase` to drive a
composition). Every mutation invalidates the parent's measurement. Mirrors
`androidx.compose.ui.node.UiApplier`. -/
def applier (root : LayoutNode) : Applier LayoutNode where
  root
  insert p i ch := do
    ch.modifyData fun d => { d with parent := some p }
    p.modifyData fun d => { d with children := d.children.insertIdx! i ch }
    p.markNeedsRemeasure
  remove p i count := do
    let d ← p.data
    for j in [i : i + count] do
      d.children[j]!.severParentLinks
    p.modifyData fun dd => { dd with children := removeRange dd.children i count }
    p.markNeedsRemeasure
  move p src dst count := do
    p.modifyData fun d => { d with children := moveRange d.children src dst count }
    p.markNeedsRemeasure
  -- Composition disposal detaches the whole tree (cancels input coroutines).
  onClear := root.severParentLinks

/-! ## Measurement -/

/-- Whether some child carries a dirty flag — `measureIn`'s guard against
clearing `needsRelayout` while a mark raised during the pass still points
through this node (see the module docstring's dirty-tracking invariant). -/
private def anyChildDirty (n : LayoutNode) : IO Bool := do
  (← n.data).children.anyM fun ch => do
    let cd ← ch.data
    return cd.needsRemeasure || cd.needsRelayout

/-- Result of measuring a suffix of the wrapper chain: the wrapper's size,
the accumulated offset to the content coordinate space, and the resolved
draw elements (offsets relative to this wrapper). -/
private structure ChainMeasured where
  size : IntSize
  contentOffset : IntOffset := .zero
  draws : Array ResolvedDraw := #[]

/-- Wrap the result in an enclosing layout wrapper of the given `size` that
places its inner content at `po`. -/
private def ChainMeasured.reframe (r : ChainMeasured) (size : IntSize) (po : IntOffset) :
    ChainMeasured :=
  { size
    contentOffset := r.contentOffset + po
    draws := if po == IntOffset.zero then r.draws
             else r.draws.map fun rd => { rd with offset := rd.offset + po } }

mutual

/-- Measure the wrapper chain from element `i` inward. Each layout element
mirrors its Compose modifier-node analog (cited per case). -/
private partial def measureChain (n : LayoutNode) (density : Density)
    (elems : Array Modifier.Elem) (i : Nat) (c : Constraints) : IO ChainMeasured := do
  if hlt : i < elems.size then
    match elems[i] with
    | .draw _ | .pointer _ | .focus _ | .semantics _ =>
      -- Non-layout elements never affect geometry; record them at the size
      -- of the wrapper they decorate (draw walk + hit-test walk).
      let r ← measureChain n density elems (i + 1) c
      return { r with draws := #[⟨i, .zero, r.size⟩] ++ r.draws }
    | .layout le =>
      let px (dp : Dp) : Int32 := density.dpRoundToPx dp
      match le with
      -- `PaddingNode`: reserve space, clamp the padded size back into `c`.
      | .padding l t rt b =>
        let (lp, tp, rp, bp) := (px l, px t, px rt, px b)
        let inner ← measureChain n density elems (i + 1) (c.offset (-(lp + rp)) (-(tp + bp)))
        return inner.reframe
          ⟨c.constrainWidth (inner.size.width + lp + rp),
           c.constrainHeight (inner.size.height + tp + bp)⟩
          ⟨lp, tp⟩
      -- `SizeNode` (enforce incoming): fix the given axes, clamped by `c`.
      | .size w? h? =>
        let target : Constraints :=
          { minWidth := (w?.map px).getD 0, maxWidth := (w?.map px).getD Constraints.infinity
            minHeight := (h?.map px).getD 0, maxHeight := (h?.map px).getD Constraints.infinity }
        measureChain n density elems (i + 1) (c.constrainBounds target)
      -- `SizeNode` for `sizeIn`: bound the given edges, clamped by `c`.
      | .sizeIn minW maxW minH maxH =>
        let target : Constraints :=
          { minWidth := (minW.map px).getD 0, maxWidth := (maxW.map px).getD Constraints.infinity
            minHeight := (minH.map px).getD 0, maxHeight := (maxH.map px).getD Constraints.infinity }
        measureChain n density elems (i + 1) (c.constrainBounds target)
      -- `SizeNode` (no enforce): override `c`; the reported size is coerced
      -- back into `c` with overflowing content centered (Compose's
      -- `apparentToRealOffset`).
      | .requiredSize w? h? =>
        let target : Constraints :=
          { minWidth := (w?.map px).getD c.minWidth, maxWidth := (w?.map px).getD c.maxWidth
            minHeight := (h?.map px).getD c.minHeight, maxHeight := (h?.map px).getD c.maxHeight }
        let inner ← measureChain n density elems (i + 1) target
        let reported := c.constrain inner.size
        return inner.reframe reported
          ⟨(reported.width - inner.size.width) / 2, (reported.height - inner.size.height) / 2⟩
      -- `FillNode`: on a bounded axis, fix to `fraction` of the maximum.
      | .fill wf? hf? =>
        let axis (f? : Option Float32) (mn mx : Int32) (bounded : Bool) : Int32 × Int32 :=
          match f? with
          | some f =>
            if bounded then
              let v := min (max (roundHalfUp (mx.toFloat32 * f)) mn) mx
              (v, v)
            else (mn, mx)
          | none => (mn, mx)
        let (minW, maxW) := axis wf? c.minWidth c.maxWidth c.hasBoundedWidth
        let (minH, maxH) := axis hf? c.minHeight c.maxHeight c.hasBoundedHeight
        measureChain n density elems (i + 1)
          { minWidth := minW, maxWidth := maxW, minHeight := minH, maxHeight := maxH }
      -- `WrapContentNode`: content measures loose, aligns inside the bounds.
      | .wrapContent align =>
        let inner ← measureChain n density elems (i + 1) c.loosen
        let wrapper := c.constrain inner.size
        return inner.reframe wrapper (align.align inner.size wrapper)
      -- `OffsetNode`: displace content, keep the measured size.
      | .offset x y =>
        let inner ← measureChain n density elems (i + 1) c
        return inner.reframe inner.size ⟨px x, px y⟩
      -- Parent data is consumed by the parent's policy, not the chain.
      | .parentData _ => measureChain n density elems (i + 1) c
      -- `Modifier.customLayout` (the generic hook, e.g. scroll): the block
      -- measures the inner chain — possibly several times (an intrinsic
      -- probe, then the real pass); the last call wins — and reports
      -- (size, content offset).
      | .custom _ blk =>
        let innerRef ← IO.mkRef (none : Option ChainMeasured)
        let measureInner (cc : Constraints) : IO IntSize := do
          let r ← measureChain n density elems (i + 1) cc
          innerRef.set (some r)
          return r.size
        let (size, po) ← blk.run density c measureInner
        let inner ← match ← innerRef.get with
          | some r => pure r
          -- Contract violation (block never measured): measure with the
          -- incoming constraints so the chain still resolves.
          | none => measureChain n density elems (i + 1) c
        return inner.reframe size po
  else
    measureInner n c

/-- The innermost measurable: runs the node's measure policy over its
children and immediately executes the returned placement block. -/
private partial def measureInner (n : LayoutNode) (c : Constraints) : IO ChainMeasured := do
  let d ← n.data
  let measurables ← d.children.mapM fun ch => do
    return { parentData := (← ch.data).modifier.parentData
             measure := fun cc => do
               let cd ← ch.data
               if cd.density != d.density then
                 ch.modifyData fun x => { x with density := d.density, needsRemeasure := true }
               let sz ← ch.measureIn cc
               return { width := sz.width, height := sz.height
                        placeAt := ch.setPosition } }
  let res ← d.policy { density := d.density } measurables c
  res.placement
  return { size := res.size }

/-- Measure the node with `c`, honoring the caches: short-circuits when the
constraints are unchanged and nothing is dirty; descends through
`needsRelayout` re-measuring dirty descendants in place, re-running this
node's own measure only if a descendant's size changed. `needsRelayout` is
cleared only when the descent left no child dirty — a measure block's state
write can re-dirty an already-visited sibling, and clearing then would
disconnect it from every future pass. -/
partial def measureIn (n : LayoutNode) (c : Constraints) : IO IntSize := do
  let d ← n.data
  if !d.needsRemeasure && d.lastConstraints == some c then
    if d.needsRelayout then
      if ← n.remeasureDirtyChildren then
        n.fullMeasure c
      else
        unless ← n.anyChildDirty do
          n.modifyData fun x => { x with needsRelayout := false }
        return d.size
    else
      return d.size
  else
    n.fullMeasure c

/-- Unconditionally re-measure: fold the wrapper chain under this node's read
observation (state reads in measure/placement invalidate exactly this node)
and refresh the caches. -/
private partial def fullMeasure (n : LayoutNode) (c : Constraints) : IO IntSize := do
  n.modifyData fun d =>
    { d with needsRemeasure := false, needsRelayout := false, lastConstraints := some c }
  let d ← n.data
  let r ← d.registry.observe (measureChain n d.density d.modifier.elems 0 c)
  n.modifyData fun x =>
    { x with size := r.size, contentOffset := r.contentOffset, resolvedDraws := r.draws }
  return r.size

/-- Re-measure dirty children with their cached constraints; `true` iff some
child's size changed (forcing this node's own remeasure). The downward
"relayout" half of the propagation rule. -/
private partial def remeasureDirtyChildren (n : LayoutNode) : IO Bool := do
  let d ← n.data
  let mut changed := false
  for ch in d.children do
    let cd ← ch.data
    if cd.needsRemeasure || cd.needsRelayout then
      match cd.lastConstraints with
      | none => changed := true -- never measured: only a full pass can size it
      | some cc =>
        if (← ch.measureIn cc) != cd.size then
          changed := true
  return changed

end

/-- Root measure pass: measure the whole tree under `constraints` at
`density` (a density change invalidates cached measurements as it
propagates). The M5 app loop calls this once per dirty frame; tests call it
directly. Dirty marks raised during the pass keep their path connected to
this root (`measureIn`); reporting them through the owner hook schedules the
follow-up frame that processes them. -/
def remeasure (n : LayoutNode) (constraints : Constraints) (density : Density := {}) :
    IO IntSize := do
  if (← n.data).density != density then
    n.modifyData fun d => { d with density }
    n.markNeedsRemeasure
  let size ← n.measureIn constraints
  let d ← n.data
  if d.needsRemeasure || d.needsRelayout then
    if let some notify := d.onRequestRemeasure then notify
  return size

/-- Reconcile modifier and policy from composition (the `emitNode` update
phase): a layout-affecting modifier change or a policy-input change
invalidates measurement. A draw-only change needs no dirty flag: the
recomposition that delivered it already scheduled a frame, the draw walk
reads the chain fresh, and the mesh cache keys off the new element values.
`none` policy inputs are conservatively treated as changed every time
(Compose's capturing-lambda `set(measurePolicy)` behavior). -/
def update (n : LayoutNode) (modifier : Modifier) (policy : MeasurePolicy)
    (policyInputs : Option UInt64 := none) : IO Unit := do
  let d ← n.data
  let policyChanged :=
    match d.policyInputs, policyInputs with
    | some a, some b => a != b
    | _, _ => true
  let layoutChanged := !Modifier.layoutEq d.modifier modifier
  n.modifyData fun x => { x with modifier, policy, policyInputs }
  if layoutChanged || policyChanged then
    n.markNeedsRemeasure

end LayoutNode

end Compose
