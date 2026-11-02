import Std.Tactic.BVDecide
/-!
# ARM (32-bit): constant folding of `MVNshiftRA` drops the complement (finding ARM-MVNSHIFTRA-CONST)

`ARM.rules` (go1.16 .. master `babb75be`):

    (MVNshiftLL (MOVWconst [c]) [d]) => (MOVWconst [^(c<<uint64(d))])
    (MVNshiftRL (MOVWconst [c]) [d]) => (MOVWconst [^int32(uint32(c)>>uint64(d))])
    (MVNshiftRA (MOVWconst [c]) [d]) => (MOVWconst [int32(c)>>uint64(d)])        -- missing ^

`MVNshiftRA x [d]` computes `^(x >> d)` (arithmetic shift, then bitwise NOT). The RA fold omits
the complement; go1.15 had `(MOVWconst [^int64(int32(c)>>uint64(d))])`, and the `^` was lost when
the rules moved to typed AuxInts in go1.16. Reachable through the 32-bit decomposition of `Ctz64`
(`Zeromask` lowers to `SRAconst [31]`, then `Com32` merges into `MVNshiftRA [31]`): when the low
word folds to a constant during `lower`, `bits.TrailingZeros64(0)` evaluates to 32 instead of 64.
-/
namespace Go.Compiler.ARMMvnShift

/-- `MVNshiftRA x [d]` as executed: complement of the arithmetic right shift. -/
def mvnShiftRA (x : BitVec 32) (d : BitVec 32) : BitVec 32 := ~~~ (x.sshiftRight' d)

/-- The fold as written (no complement) and as fixed. -/
def foldBuggy (c : BitVec 32) (d : BitVec 32) : BitVec 32 := c.sshiftRight' d
def foldFixed (c : BitVec 32) (d : BitVec 32) : BitVec 32 := ~~~ (c.sshiftRight' d)

/-- Kernel-checked counterexample: `c = 0, d = 31` (the `Zeromask` case). -/
theorem fold_refuted : foldBuggy 0 31 = 0 ∧ mvnShiftRA 0 31 = 0xFFFFFFFF := by decide

theorem fold_unsound : ¬ ∀ c d : BitVec 32, d < 32 → foldBuggy c d = mvnShiftRA c d := by
  intro h; have := h 0 31 (by decide); revert this; decide

/-- The fixed fold equals the instruction for every constant and every count. -/
theorem fold_fixed (c d : BitVec 32) : foldFixed c d = mvnShiftRA c d := rfl

/-- The buggy fold is never right: it always differs from the instruction (bitwise complement). -/
theorem fold_always_wrong (c d : BitVec 32) : foldBuggy c d ≠ mvnShiftRA c d := by
  unfold foldBuggy mvnShiftRA; bv_decide (config := {timeout := 120})

/-- End-to-end: 32-bit `Ctz64` decomposition with low word 0 and high word 0 is 64 only with the
complement: `Ctz32 lo + (^(Zeromask lo) & 32)` where `Zeromask 0 = 0`. -/
theorem ctz64_zero_needs_complement :
    (32 : BitVec 32) + (mvnShiftRA 0 31 &&& 32) = 64 ∧ (32 : BitVec 32) + (foldBuggy 0 31 &&& 32) = 32 := by
  decide

end Go.Compiler.ARMMvnShift
