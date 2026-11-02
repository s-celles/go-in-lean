import Std.Tactic.BVDecide
/-!
# prove: a fact carried through a sign extension, then a constant truncated (finding PROVE-EXT-CONST-TRUNC)

`cmd/compile/internal/ssacompile/prove.go` (`factsTable.update`, master; identical since at least
go1.24): "Look through value-preserving extensions" repeats a fact `ext(x) op w` on the narrow `x`
with the same `w`. When `w` is a constant outside `x`'s range, the "x+delta > w" step then computes
`min = w - delta` "using integers of the correct size", i.e. `int16(w.AuxInt) - int16(delta)` for a
16-bit `x`, truncating `w`. The derived bound on `x` is false and prove decides branches wrongly.

Model (16-bit narrow value `s = x + delta`, 32-bit comparison against `w`):
* `unguarded_refuted`: the 32-bit fact `sext(x + delta) >= w` holds for `x = 0, delta = -513,
  w = -536870911`, but the derived `x >= int16(w) - delta = 514` is false (kernel-checked).
* `fits_iff`: when `w` fits in 16 bits, the 32-bit fact is equivalent to the 16-bit one — the
  condition the fix (`constFitsIn`) requires before carrying the fact over.
* `xdelta_sound`: the "x+delta >= w" derivation itself is sound at 16 bits (all of `x, delta, w`).
-/
namespace Go.Compiler.ProveExtDelta

/-- The bound prove derives from `x + delta >= w` at 16 bits: `min <= x` and/or `x <= max`. -/
def derived (x delta w : BitVec 16) : Bool :=
  let min := w - delta
  let max := (0x7FFF : BitVec 16) - delta
  if min.slt max then (min.sle x && x.sle max) else (min.sle x || x.sle max)

/-- The derivation is sound at the narrow width. -/
theorem xdelta_sound (x delta w : BitVec 16) (h : w.sle (x + delta) = true) :
    derived x delta w = true := by
  unfold derived; bv_decide (config := {timeout := 120})

/-- If the 32-bit constant fits in 16 bits, the wide fact equals the narrow one. -/
theorem fits_iff (s : BitVec 16) (w : BitVec 32) (hw : (w.setWidth 16).signExtend 32 = w) :
    w.sle (s.signExtend 32) = (w.setWidth 16).sle s := by
  bv_decide (config := {timeout := 120})

/-- Unguarded: the wide fact holds, the derived narrow bound does not. -/
theorem unguarded_refuted :
    let x : BitVec 16 := 0
    let delta : BitVec 16 := 0xFDFF          -- -513
    let w : BitVec 32 := 0xE0000001          -- -536870911
    (w.sle ((x + delta).signExtend 32) = true) ∧ derived x delta (w.setWidth 16) = false := by
  decide

end Go.Compiler.ProveExtDelta
