import Compose.Ui.Layout
import Compose.Runtime.Macro

namespace Compose

/-!
# Image composable (`Compose/Foundation/Image.lean`)

`Image` — the leaf that displays an `ImageBitmap`. Mirrors
`androidx.compose.foundation.Image`: it measures to the bitmap's intrinsic
size clamped to the incoming constraints and draws the pixels fitted into its
box per `ContentScale`.

`ContentScale.resolve` is the pure placement math: it returns the source
portion (in image pixels; `none` = the whole image) and the destination
rectangle (node-local px) for one draw. Cropping styles cut with a source
rectangle instead of a clip — exact on both backends, no scissor needed.
-/

open Draw in
/-- How an image's pixels map onto the node's box (always centered). Mirrors
`androidx.compose.ui.layout.ContentScale`. -/
inductive ContentScale where
  /-- Uniformly scale so the whole image fits inside (letterboxed). Mirrors
  `ContentScale.Fit`. -/
  | fit
  /-- Uniformly scale so the image covers the box; the overflow is cut via
  the source rect. Mirrors `ContentScale.Crop`. -/
  | crop
  /-- Stretch both axes to the box (aspect ratio not preserved). Mirrors
  `ContentScale.FillBounds`. -/
  | fillBounds
  /-- No scaling: draw at natural size, centered, cut to the box via the
  source rect. Mirrors `ContentScale.None`. -/
  | none
  deriving Repr, BEq, Inhabited

namespace ContentScale

/-- Placement of an `imgSize` image inside a `nodeSize` box: the source
portion in image pixels (`none` = whole image) and the destination rect in
node-local px. Degenerate sizes resolve to an empty destination. -/
def resolve (scale : ContentScale) (imgSize nodeSize : Size) : Option Rect × Rect :=
  let iw := imgSize.width; let ih := imgSize.height
  let nw := nodeSize.width; let nh := nodeSize.height
  if iw <= 0 || ih <= 0 || nw <= 0 || nh <= 0 then
    (Option.none, ⟨0, 0, 0, 0⟩)
  else
    -- Centered `w × h` rects in image / node space.
    let srcAt (w h : Float32) : Option Rect :=
      if w >= iw && h >= ih then Option.none
      else some ⟨(iw - w) / 2, (ih - h) / 2, (iw - w) / 2 + w, (ih - h) / 2 + h⟩
    let dstAt (w h : Float32) : Rect :=
      ⟨(nw - w) / 2, (nh - h) / 2, (nw - w) / 2 + w, (nh - h) / 2 + h⟩
    match scale with
    | .fillBounds => (Option.none, ⟨0, 0, nw, nh⟩)
    | .fit =>
      let s := min (nw / iw) (nh / ih)
      (Option.none, dstAt (iw * s) (ih * s))
    | .crop =>
      let s := max (nw / iw) (nh / ih)
      (srcAt (nw / s) (nh / s), ⟨0, 0, nw, nh⟩)
    | .none =>
      let w := min iw nw
      let h := min ih nh
      (srcAt w h, dstAt w h)

-- fit: aspect preserved, letterboxed, centered.
#guard resolve .fit ⟨2, 2⟩ ⟨4, 4⟩ == (Option.none, ⟨0, 0, 4, 4⟩)
#guard resolve .fit ⟨2, 1⟩ ⟨4, 4⟩ == (Option.none, ⟨0, 1, 4, 3⟩)
#guard resolve .fit ⟨1, 2⟩ ⟨4, 4⟩ == (Option.none, ⟨1, 0, 3, 4⟩)
-- crop: covers the box, overflow cut through the source rect.
#guard resolve .crop ⟨2, 1⟩ ⟨4, 4⟩ == (some ⟨0.5, 0, 1.5, 1⟩, ⟨0, 0, 4, 4⟩)
#guard resolve .crop ⟨2, 2⟩ ⟨4, 4⟩ == (Option.none, ⟨0, 0, 4, 4⟩)
-- fillBounds: stretched, whole image.
#guard resolve .fillBounds ⟨2, 1⟩ ⟨4, 4⟩ == (Option.none, ⟨0, 0, 4, 4⟩)
-- none: natural size — centered when it fits, mutually cut when it doesn't.
#guard resolve .none ⟨2, 2⟩ ⟨4, 4⟩ == (Option.none, ⟨1, 1, 3, 3⟩)
#guard resolve .none ⟨4, 4⟩ ⟨2, 2⟩ == (some ⟨1, 1, 3, 3⟩, ⟨0, 0, 2, 2⟩)
-- degenerate: empty destination.
#guard (resolve .fit ⟨0, 0⟩ ⟨4, 4⟩).2 == (⟨0, 0, 0, 0⟩ : Rect)

end ContentScale

/-- Display an `ImageBitmap`. The node measures to the bitmap's natural size
clamped to the constraints; `contentScale` maps the pixels onto the resulting
box and `sampling` picks the filtering for scaled draws. `desc` is the
accessibility/test description (`Matcher.desc`). Mirrors
`androidx.compose.foundation.Image`. -/
composable def Image (bitmap : Draw.ImageBitmap) (modifier : Modifier := {})
    (contentScale : ContentScale := .fit) (sampling : Draw.Sampling := .linear)
    (desc : Option String := none) : Composable Unit := do
  let modifier := match desc with
    | some _ => modifier.semantics (desc := desc)
    | none => modifier
  let policy : MeasurePolicy := fun _ _ c => do
    return { size := c.constrain ⟨Int32.ofNat bitmap.width, Int32.ofNat bitmap.height⟩ }
  let drawMod := modifier.drawBehind do
    let sz ← Draw.DrawScope.size
    let (src, dst) := contentScale.resolve bitmap.size sz
    Draw.DrawScope.drawImage bitmap dst src sampling
  let scaleK : UInt64 := match contentScale with
    | .fit => 0 | .crop => 1 | .fillBounds => 2 | .none => 3
  Layout drawMod policy
    (policyInputs := some (mixKeys (UInt64.ofNat bitmap.id)
      (mixKeys scaleK (if sampling == .nearest then 1 else 0))))

end Compose
