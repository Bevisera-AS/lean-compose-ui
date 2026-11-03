module

public import Compose.Ui.Draw.Path
public meta import Compose.Ui.Draw.Path

public section

namespace Compose.Draw

/-!
# SVG path data → `Path`

`PathData.parse?` turns SVG `d` attribute strings — the interchange format
of every icon pipeline (Material Symbols exports, `ImageVector` path data) —
into a `Compose.Path`. Any Material icon becomes one pasted string (see
`Compose.Material.Icons`).

Supported commands: `M m L l H h V v C c S s Q q T t A a Z z`, comma/whitespace
separation, implicit repetition (extra pairs after `M`/`m` continue as
lineto, per the SVG grammar), smooth control-point reflection for `S`/`T`.
Elliptical arcs (`A`/`a`) become cubic Béziers, at most a quarter turn each
(SVG 1.1 implementation notes F.6.5–F.6.6), so outline icon sets such as
Tabler paste unchanged.
-/

namespace PathData

/-- Interpreter state: verbs so far, current point, subpath start, and the
previous control points `S`/`T` reflect. -/
private structure St where
  verbs : Array PathVerb := #[]
  cur : Offset := .zero
  start : Offset := .zero
  prevCubic : Option Offset := none
  prevQuad : Option Offset := none

/-- An SVG elliptical arc from `p0` to `p` as cubic Béziers of at most a quarter
turn each. Degenerate radii draw a line; equal endpoints draw nothing. -/
def arcToCubics (p0 : Offset) (rx ry phiDeg : Float) (large sweep : Bool) (p : Offset) :
    Array PathVerb := Id.run do
  let (x0, y0, x, y) := (p0.x.toFloat, p0.y.toFloat, p.x.toFloat, p.y.toFloat)
  if x0 == x && y0 == y then return #[]
  if rx == 0 || ry == 0 then return #[.lineTo p]
  let pi : Float := 3.141592653589793
  let phi := phiDeg * pi / 180
  let (cs, sn) := (Float.cos phi, Float.sin phi)
  let (dx2, dy2) := ((x0 - x) / 2, (y0 - y) / 2)
  let x1 := cs * dx2 + sn * dy2
  let y1 := -sn * dx2 + cs * dy2
  let (rx, ry) := (rx.abs, ry.abs)
  let lam := x1 * x1 / (rx * rx) + y1 * y1 / (ry * ry)
  let (rx, ry) := if lam > 1 then (rx * lam.sqrt, ry * lam.sqrt) else (rx, ry)
  let num := rx * rx * ry * ry - rx * rx * y1 * y1 - ry * ry * x1 * x1
  let den := rx * rx * y1 * y1 + ry * ry * x1 * x1
  let coef := (if den == 0 then 0 else (max 0 (num / den)).sqrt) * (if large == sweep then -1 else 1)
  let (cxp, cyp) := (coef * rx * y1 / ry, -coef * ry * x1 / rx)
  let cx := cs * cxp - sn * cyp + (x0 + x) / 2
  let cy := sn * cxp + cs * cyp + (y0 + y) / 2
  let angle (ux uy vx vy : Float) : Float := Float.atan2 (ux * vy - uy * vx) (ux * vx + uy * vy)
  let (ux, uy) := ((x1 - cxp) / rx, (y1 - cyp) / ry)
  let (vx, vy) := ((-x1 - cxp) / rx, (-y1 - cyp) / ry)
  let t1 := angle 1 0 ux uy
  let d0 := angle ux uy vx vy
  let delta := if !sweep && d0 > 0 then d0 - 2 * pi else if sweep && d0 < 0 then d0 + 2 * pi else d0
  let n := max 1 (delta.abs / (pi / 2)).ceil.toUInt64.toNat
  let step := delta / n.toFloat
  let k := 4 / 3 * Float.tan (step / 4)
  let pointAt (t : Float) : Float × Float :=
    (cx + rx * cs * Float.cos t - ry * sn * Float.sin t,
     cy + rx * sn * Float.cos t + ry * cs * Float.sin t)
  let tangent (t : Float) : Float × Float :=
    (-rx * cs * Float.sin t - ry * sn * Float.cos t,
     -rx * sn * Float.sin t + ry * cs * Float.cos t)
  let off (q : Float × Float) : Offset := ⟨q.1.toFloat32, q.2.toFloat32⟩
  let mut out := #[]
  for i in [0:n] do
    let a := t1 + i.toFloat * step
    let b := a + step
    let (pa, da, pb, db) := (pointAt a, tangent a, pointAt b, tangent b)
    let c1 := (pa.1 + k * da.1, pa.2 + k * da.2)
    let c2 := (pb.1 - k * db.1, pb.2 - k * db.2)
    out := out.push (.cubicTo (off c1) (off c2) (if i + 1 == n then p else off pb))
  return out

private def isCmd (c : Char) : Bool :=
  "MmLlHhVvCcSsQqTtZzAa".toList.contains c

private def skipSep (cs : List Char) : List Char :=
  cs.dropWhile fun c => c.isWhitespace || c == ','

/-- Scan one number (`-?d*.?d*` with optional exponent). SVG allows a sign
to start the next number without separation (`10-5`), which `span`-based
scanning handles by stopping at the sign. -/
private def scanNum (cs : List Char) : Option (Float × List Char) := do
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let (ip, cs) := cs.span Char.isDigit
  let (fp, cs) := match cs with
    | '.' :: r => r.span Char.isDigit
    | r => ([], r)
  if ip.isEmpty && fp.isEmpty then none
  else
    let (e, cs) := match cs with
      | 'e' :: r | 'E' :: r =>
        let (en, r) := match r with
          | '-' :: r' => (true, r')
          | '+' :: r' => (false, r')
          | r' => (false, r')
        let (ed, r') := r.span Char.isDigit
        if ed.isEmpty then (0, cs)
        else ((if en then -(digits ed : Int) else digits ed), r')
      | r => ((0 : Int), r)
    let m := digits (ip ++ fp)
    let dec : Int := e - fp.length
    let x := Float.ofScientific m (dec < 0) dec.natAbs
    some (if neg then -x else x, cs)
where
  digits (cs : List Char) : Nat :=
    cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Scan `n` numbers as `Float32`s. -/
private def scanArgs : Nat → List Char → Option (Array Float32 × List Char)
  | 0, cs => some (#[], cs)
  | n + 1, cs => do
    let (x, cs) ← scanNum (skipSep cs)
    let (xs, cs) ← scanArgs n cs
    some (#[x.toFloat32] ++ xs, cs)

/-- Number of arguments each command consumes per repetition. -/
private def argc : Char → Nat
  | 'M' | 'm' | 'L' | 'l' | 'T' | 't' => 2
  | 'H' | 'h' | 'V' | 'v' => 1
  | 'S' | 's' | 'Q' | 'q' => 4
  | 'C' | 'c' => 6
  | 'A' | 'a' => 7
  | _ => 0

/-- Execute one repetition of `cmd` with `a` (already `argc` long). -/
private def step (st : St) (cmd : Char) (a : Array Float32) : Option St := do
  let rel := cmd.isLower
  let abs2 (i : Nat) : Offset :=
    let p : Offset := ⟨a[i]!, a[i+1]!⟩
    if rel then st.cur + p else p
  let push (v : PathVerb) (cur : Offset)
      (pc : Option Offset := none) (pq : Option Offset := none) : St :=
    { st with verbs := st.verbs.push v, cur, prevCubic := pc, prevQuad := pq }
  match cmd.toLower with
  | 'm' =>
    let p := abs2 0
    return { push (.moveTo p) p with start := p }
  | 'l' => return push (.lineTo (abs2 0)) (abs2 0)
  | 'h' =>
    let x := if rel then st.cur.x + a[0]! else a[0]!
    return push (.lineTo ⟨x, st.cur.y⟩) ⟨x, st.cur.y⟩
  | 'v' =>
    let y := if rel then st.cur.y + a[0]! else a[0]!
    return push (.lineTo ⟨st.cur.x, y⟩) ⟨st.cur.x, y⟩
  | 'c' =>
    let (c1, c2, p) := (abs2 0, abs2 2, abs2 4)
    return push (.cubicTo c1 c2 p) p (pc := some c2)
  | 's' =>
    let c1 := match st.prevCubic with
      | some c => st.cur + (st.cur - c)
      | none => st.cur
    let (c2, p) := (abs2 0, abs2 2)
    return push (.cubicTo c1 c2 p) p (pc := some c2)
  | 'q' =>
    let (c, p) := (abs2 0, abs2 2)
    return push (.quadTo c p) p (pq := some c)
  | 't' =>
    let c := match st.prevQuad with
      | some c => st.cur + (st.cur - c)
      | none => st.cur
    let p := abs2 0
    return push (.quadTo c p) p (pq := some c)
  | 'a' =>
    let p := abs2 5
    let arc := arcToCubics st.cur a[0]!.toFloat a[1]!.toFloat a[2]!.toFloat (a[3]! != 0) (a[4]! != 0) p
    return { st with verbs := st.verbs ++ arc, cur := p, prevCubic := none, prevQuad := none }
  | _ => none

/-- The command implicit repetition continues as (`M`→`L`, `m`→`l`). -/
private def continuation (cmd : Char) : Char :=
  match cmd with
  | 'M' => 'L'
  | 'm' => 'l'
  | c => c

private partial def run (cs : List Char) (cmd : Char) (st : St) : Option St := do
  match skipSep cs with
  | [] => some st
  | c :: rest =>
    if c == 'Z' || c == 'z' then
      run rest ' ' { st with verbs := st.verbs.push .close, cur := st.start,
                             prevCubic := none, prevQuad := none }
    else if isCmd c then
      if argc c == 0 then none  -- any future zero-arg strays
      else run rest c st
    else if cmd == ' ' then none  -- numbers need a current command
    else do
      let (a, rest') ← scanArgs (argc cmd) (c :: rest)
      run rest' (continuation cmd) (← step st cmd a)

/-- Parse SVG path data; `none` on any unsupported command or malformed
number stream. -/
def parse? (d : String) (fillRule : FillRule := .nonZero) : Option Path := do
  let st ← run d.toList ' ' {}
  some { verbs := st.verbs, fillRule }

#guard parse? "M2 4L5 6Z"
  == some { verbs := #[.moveTo ⟨2, 4⟩, .lineTo ⟨5, 6⟩, .close] }
#guard parse? "m2 4l3 2z"
  == some { verbs := #[.moveTo ⟨2, 4⟩, .lineTo ⟨5, 6⟩, .close] }
#guard parse? "M8 5v14l11-7z"   -- play_arrow: mixed rel/abs, unseparated sign
  == some { verbs := #[.moveTo ⟨8, 5⟩, .lineTo ⟨8, 19⟩, .lineTo ⟨19, 12⟩, .close] }
#guard parse? "M1 1 2 2 3 3"    -- implicit lineto continuation after M
  == some { verbs := #[.moveTo ⟨1, 1⟩, .lineTo ⟨2, 2⟩, .lineTo ⟨3, 3⟩] }
#guard parse? "M0 0H4V4"        -- H/V axis moves
  == some { verbs := #[.moveTo ⟨0, 0⟩, .lineTo ⟨4, 0⟩, .lineTo ⟨4, 4⟩] }
#guard parse? "M0 0C1 2 3 4 5 6S9 10 11 12"  -- smooth cubic reflects c2
  == some { verbs := #[.moveTo ⟨0, 0⟩, .cubicTo ⟨1, 2⟩ ⟨3, 4⟩ ⟨5, 6⟩,
                       .cubicTo ⟨7, 8⟩ ⟨9, 10⟩ ⟨11, 12⟩] }
#guard parse? "M0 0Q1 2 3 4T5 6"             -- smooth quad reflects control
  == some { verbs := #[.moveTo ⟨0, 0⟩, .quadTo ⟨1, 2⟩ ⟨3, 4⟩,
                       .quadTo ⟨5, 6⟩ ⟨5, 6⟩] }
-- a half circle is two quarter-turn cubics ending exactly at the endpoint
#guard (parse? "M0 0A5 5 0 0 1 10 0").map (·.verbs.size) == some 3
#guard match (parse? "M0 0A5 5 0 0 1 10 0").bind (·.verbs.back?) with
  | some (PathVerb.cubicTo _ _ q) => q == ⟨10, 0⟩
  | _ => false
-- a full Tabler circle (two arcs) is four cubics after the move
#guard (parse? "M3 12a9 9 0 1 0 18 0a9 9 0 1 0 -18 0").map (·.verbs.size) == some 5
#guard parse? "M0 0A0 5 0 0 1 10 0"           -- zero radius draws a line
  == some { verbs := #[.moveTo ⟨0, 0⟩, .lineTo ⟨10, 0⟩] }
#guard parse? "M0 0L1" == none                -- truncated args
#guard parse? "1 2 3" == none                 -- numbers before any command
#guard parse? "M1.5-2.5e1l.5.5"               -- exponent, terse decimals
  == some { verbs := #[.moveTo ⟨1.5, -25⟩, .lineTo ⟨2, -24.5⟩] }

end PathData

end Compose.Draw

end
