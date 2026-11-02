import Std.Tactic.BVDecide
/-!
# `((x >> c) & d) << e` rules (generic.rules:522-530, go1.25.5): counterexample and fix

The rules compare the int64 AuxInts `c`, `e` with SIGNED `c >= e` / `c < e`, but shift counts
are unsigned: a constant count `c ≥ 2^63` (int64 AuxInt < 0) selects the `c < e` branch and the
rewrite computes `x << (e - c)` / `x >> (c - e)` with wrapped amounts. Finding
`findings/SSA-SHIFTMASK-SIGNED-COUNT` (reproduced on go1.25.5 arm64 and amd64, also via inlining).

* `rule527_refuted`: kernel-checked witness for the 64-bit signed instance
  (x = -1, c = 2^63, d = 3, e = 1: rule gives 0, Go semantics 6), the inputs of the Go reproducer.
* `fixed_*`: the same rules are sound when both counts are below 2^63
  (`0 <= c && 0 <= e`, i.e. the comparisons made unsigned on the reachable range).
-/
namespace Go.Compiler.ShiftMask

/-- The reproducer's inputs (x = -1, c = 2^63, d = 3, e = 1) distinguish the two sides of
generic.rules:527 (64-bit signed instance). The values are given as hypotheses so that no
evaluator ever computes a shift by 2^63 (Lean's `Nat.shiftLeft` refuses such exponents). -/
theorem rule527_counterexample (x c d e : BitVec 64) (hx : x = 0xFFFFFFFFFFFFFFFF)
    (hc : c = 0x8000000000000000) (hd : d = 3) (he : e = 1) :
    c.slt e = true ∧ ((x.sshiftRight' c) &&& d) <<< e ≠ (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:527 (64-bit signed instance) is unsound as written. -/
theorem rule527_refuted :
    ¬ ∀ (x : BitVec 64) (c d e : BitVec 64), c.slt e = true →
      ((x.sshiftRight' c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  intro h
  generalize hx : (0xFFFFFFFFFFFFFFFF : BitVec 64) = x
  generalize hc : (0x8000000000000000 : BitVec 64) = c
  have ⟨hlt, hne⟩ := rule527_counterexample x c 3 1 hx.symm hc.symm rfl rfl
  exact hne (h x c 3 1 hlt)

/-- generic.rules:523 with `c >= e`, fixed: also `0 <= c && 0 <= e` (64-bit, signed inner shift). -/
theorem fixed_ge_64s (x d : BitVec 64) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x.sshiftRight' (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:527 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_64s (x d : BitVec 64) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:523 with `c >= e`, fixed: also `0 <= c && 0 <= e` (64-bit, unsigned inner shift). -/
theorem fixed_ge_64u (x d : BitVec 64) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x >>> c) &&& d) <<< e = (x >>> (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:527 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_64u (x d : BitVec 64) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x >>> c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:524 with `c >= e`, fixed: also `0 <= c && 0 <= e` (32-bit, signed inner shift). -/
theorem fixed_ge_32s (x d : BitVec 32) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x.sshiftRight' (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:528 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_32s (x d : BitVec 32) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:524 with `c >= e`, fixed: also `0 <= c && 0 <= e` (32-bit, unsigned inner shift). -/
theorem fixed_ge_32u (x d : BitVec 32) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x >>> c) &&& d) <<< e = (x >>> (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:528 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_32u (x d : BitVec 32) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x >>> c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:525 with `c >= e`, fixed: also `0 <= c && 0 <= e` (16-bit, signed inner shift). -/
theorem fixed_ge_16s (x d : BitVec 16) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x.sshiftRight' (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:529 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_16s (x d : BitVec 16) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:525 with `c >= e`, fixed: also `0 <= c && 0 <= e` (16-bit, unsigned inner shift). -/
theorem fixed_ge_16u (x d : BitVec 16) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x >>> c) &&& d) <<< e = (x >>> (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:529 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_16u (x d : BitVec 16) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x >>> c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:526 with `c >= e`, fixed: also `0 <= c && 0 <= e` (8-bit, signed inner shift). -/
theorem fixed_ge_8s (x d : BitVec 8) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x.sshiftRight' (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:530 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_8s (x d : BitVec 8) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x.sshiftRight' c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

/-- generic.rules:526 with `c >= e`, fixed: also `0 <= c && 0 <= e` (8-bit, unsigned inner shift). -/
theorem fixed_ge_8u (x d : BitVec 8) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : e.sle c = true) :
    ((x >>> c) &&& d) <<< e = (x >>> (c - e)) &&& (d <<< e) := by
  bv_decide
/-- generic.rules:530 with `c < e`, fixed: also `0 <= c && 0 <= e`. -/
theorem fixed_lt_8u (x d : BitVec 8) (c e : BitVec 64) (hc : c.msb = false) (he : e.msb = false)
    (h : c.slt e = true) :
    ((x >>> c) &&& d) <<< e = (x <<< (e - c)) &&& (d <<< e) := by
  bv_decide

end Go.Compiler.ShiftMask
