import Std.Tactic.BVDecide
import GoInLean.Properties.Bits
/-!
# `Rem64`, `Rem32`, `Div32` (gaps reported by review/bits-model-review.md)
-/
namespace Go.Bits.Properties.DivRem
open Go Go.Bits Go.Bits.Properties

theorem umod_lt {w : Nat} (a y : BitVec w) (hy : y ≠ 0) : a % y < y := by
  rw [BitVec.lt_def, BitVec.toNat_umod]
  apply Nat.mod_lt
  rcases Nat.eq_zero_or_pos y.toNat with h | h
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hy
  · exact h

/-- BITS-REM-PANIC: `Rem64` panics with `divideError` iff `y == 0` and, per its doc,
"unlike Div64, it doesn't panic on a quotient overflow" — for every half-width. -/
theorem remGeneric_divide (h : Nat) (hi lo y : BitVec (2*h)) (hy : y = 0) :
    remGeneric h hi lo y = .error .divideError := by
  simp [remGeneric, hy]

theorem remGeneric_no_panic (h : Nat) (hi lo y : BitVec (2*h)) (hy : y ≠ 0) :
    ∃ r, remGeneric h hi lo y = .ok r := by
  have hy' : ¬ (y = 0#(2*h)) := hy
  obtain ⟨r, hr⟩ := divGeneric_ok h (hi % y) lo y hy (umod_lt hi y hy)
  exact ⟨r.2, by simp [remGeneric, hy', hr, Except.map]⟩

theorem concat16_toNat (a b : BitVec 8) :
    (a.zeroExtend (4*4) <<< (2*4) ||| b.zeroExtend (4*4)).toNat = a.toNat * 2^8 + b.toNat := by
  have h : a.zeroExtend (4*4) <<< (2*4) ||| b.zeroExtend (4*4) = a ++ b := by bv_decide
  rw [h, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

/-- BITS-REM-8: `Rem` at width 8 is the remainder of the 16-bit dividend, also when the
quotient would overflow (`hi ≥ y`). -/
theorem remGeneric_4_spec (hi lo y : BitVec 8) (hy : y ≠ 0) :
    remGeneric 4 hi lo y = .ok (divSpec 4 hi lo y).2 := by
  have hy' : ¬ (y = 0#8) := hy
  have hd := divGeneric_4_spec (hi % y) lo y hy (umod_lt hi y hy)
  simp only [remGeneric, hy', ↓reduceIte, hd, Except.map]
  rw [if_neg hy]
  congr 1
  dsimp only [divSpec]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, concat16_toNat, concat16_toNat, BitVec.toNat_umod]
  have hyz : (y.zeroExtend (4*4)).toNat = y.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)
  rw [hyz, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- BITS-REM32: `Rem32` = remainder of the 64-bit dividend; panics iff `y == 0`. -/
theorem Rem32_spec (hi lo y : uint32) (hy : y ≠ 0) :
    Rem32 hi lo y = .ok (((hi.zeroExtend 64 <<< 32 ||| lo.zeroExtend 64) % y.zeroExtend 64).setWidth 32) := by
  have hy' : ¬ (y = 0#32) := hy
  simp [Rem32, hy', Go.convU]

/-- BITS-DIV32: when `Div32` does not panic, it returns the exact quotient and remainder of
the 64-bit dividend `hi·2^32 + lo` (stated over `Nat`). -/
theorem Div32_spec (hi lo y : uint32) (hy : y ≠ 0) (hhi : hi < y) :
    ∃ q r, Div32 hi lo y = .ok (q, r) ∧
      q.toNat = (hi.toNat * 2^32 + lo.toNat) / y.toNat ∧
      r.toNat = (hi.toNat * 2^32 + lo.toNat) % y.toNat := by
  have hy' : ¬ (y = 0#32) := hy
  have hle : ¬ (y ≤ hi) := BitVec.not_le.mpr hhi
  have hz : ((Go.convU 64 hi <<< 32) ||| Go.convU 64 lo).toNat = hi.toNat * 2^32 + lo.toNat := by
    have : (Go.convU 64 hi <<< 32) ||| Go.convU 64 lo = (Go.convU 64 hi <<< 32) + Go.convU 64 lo := by
      unfold Go.convU; bv_decide
    rw [this, BitVec.toNat_add, BitVec.toNat_shiftLeft]
    simp only [Go.convU, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    have := hi.isLt; have := lo.isLt
    rw [Nat.mod_eq_of_lt (by omega : hi.toNat < 2^64), Nat.mod_eq_of_lt (by omega : lo.toNat < 2^64)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hyn : (Go.convU 64 y).toNat = y.toNat := by
    simp only [Go.convU, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)
  have hypos : 0 < y.toNat := by have := BitVec.lt_def.mp hhi; omega
  have hq : (hi.toNat * 2^32 + lo.toNat) / y.toNat < 2^32 := by
    rw [Nat.div_lt_iff_lt_mul hypos]
    have := BitVec.lt_def.mp hhi; have := lo.isLt
    calc hi.toNat * 2^32 + lo.toNat < (hi.toNat + 1) * 2^32 := by omega
      _ ≤ y.toNat * 2^32 := Nat.mul_le_mul_right _ (by omega)
      _ = 2^32 * y.toNat := Nat.mul_comm _ _
  have hr : (hi.toNat * 2^32 + lo.toNat) % y.toNat < 2^32 := by
    have := Nat.mod_lt (hi.toNat * 2^32 + lo.toNat) hypos; have := y.isLt; omega
  refine ⟨_, _, by simp only [Div32, hle, and_false, ↓reduceIte]; rw [if_neg hy], ?_, ?_⟩
  all_goals simp only [Go.convU] at hz
  all_goals have hy64 : y.toNat % 2^64 = y.toNat := Nat.mod_eq_of_lt (by have := y.isLt; omega)
  · simp only [Go.convU, BitVec.toNat_setWidth, BitVec.toNat_udiv, hz, hy64]
    exact Nat.mod_eq_of_lt hq
  · simp only [Go.convU, BitVec.toNat_setWidth, BitVec.toNat_umod, hz, hy64]
    exact Nat.mod_eq_of_lt hr

end Go.Bits.Properties.DivRem
