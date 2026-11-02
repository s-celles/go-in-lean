import Std.Tactic.BVDecide
import GoInLean.Compiler.AMD64
/-!
# A locally unsound AMD64 rule, protected only by its producers (finding AMD64-CMPL-SHRL-32)

`AMD64.rules:1197` (go1.25.5):
`(CMPLconst (SHRLconst _ [c]) [n]) && 0 <= n && 0 < c && c <= 32 && (1<<uint64(32-c)) <= uint64(n) => (FlagLT_ULT)`
claims the 32-bit value `x >> c` is unsigned-below `n`. The hardware masks a 32-bit shift
count to 5 bits, so `SHRLconst [32]` shifts by 0, and the claim fails. The only producer,
`AMD64.rules:791` `(SHRL x (MOV(Q|L)const [c])) => (SHRLconst [int8(c&31)] x)`, never emits 32.
(Found by the independent reviewer, review/compiler-shift-review.md; restated and checked here.)
-/
namespace Go.Compiler.AMD64Latent
open Go.Compiler

/-- `SHRLconst [c] x` as executed: count masked to 5 bits. -/
def shrlconst (c : BitVec 64) (x : BitVec 64) : BitVec 64 := X86.shrl x c

/-- The rule is sound for every count its producer can emit (`1 ≤ c ≤ 31`). -/
theorem cmpl_shrl_sound (x c n : BitVec 64) (hc0 : 0 < c) (hc : c ≤ 31) (hn : n.msb = false)
    (hcond : (1 : BitVec 64) <<< (32 - c) ≤ n) :
    (shrlconst c x).setWidth 32 < n.setWidth 32 ∨ n.toNat ≥ 2^32 := by
  unfold shrlconst
  simp only [X86.shrl, X86.put, X86.low, ↓reduceIte]
  rcases Nat.lt_or_ge n.toNat (2^32) with h | h
  · left
    have : n < 0x100000000 := BitVec.lt_def.mpr (by simpa using h)
    bv_decide (config := {timeout := 120})
  · right; exact h

/-- …and unsound for `c = 32` as the rule's own side condition allows (`n = 1`, `x = 5`). -/
theorem cmpl_shrl_c32_refuted :
    ¬ ∀ x n : BitVec 64, ((1 : BitVec 64) <<< (32 - 32) ≤ n) → (shrlconst 32 x).setWidth 32 < n.setWidth 32 := by
  intro h
  have := h 5 1 (by decide)
  revert this; unfold shrlconst; simp only [X86.shrl, X86.put, X86.low, ↓reduceIte]; decide

/-- The producer only emits counts in `[0, 31]`. -/
theorem producer_range (c : BitVec 64) : (c &&& 31) ≤ 31 := by bv_decide (config := {timeout := 120})

end Go.Compiler.AMD64Latent
