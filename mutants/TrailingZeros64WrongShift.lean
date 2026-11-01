import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
import GoInLean.Properties.Bits
open Go Go.Bits Go.BitSpec Go.Bits.Properties
set_option maxRecDepth 16384
/-- MUTANT: de Bruijn index taken as the top 5 bits (masked to 6) instead of the top 6. -/
def TrailingZeros64WrongShift (x : uint64) : int :=
  if x = 0 then 64 else
  (tab deBruijn64tab ((((x &&& -x) * deBruijn64) >>> (64 - 5)) &&& 63)).zeroExtend 64
theorem TrailingZeros64WrongShift_spec (x : uint64) : TrailingZeros64WrongShift x = ctz x := by
  dsimp only [TrailingZeros64WrongShift]
  rw [tab_deBruijn64_of_lt _ (BitVec.lt_def.mp (by bv_decide : ((((x &&& -x) * deBruijn64) >>> (64 - 5)) &&& 63) < 64#64))]
  unroll_spec; unfold deBruijn64tabFn deBruijn64; bv_decide
