import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
import GoInLean.Properties.Bits
open Go Go.Bits Go.BitSpec Go.Bits.Properties
set_option maxRecDepth 16384
/-- MUTANT: the `x >= 1<<32` step is missing. -/
def Len64NoHighHalf (x : uint64) : int :=
  let n : int := if x ≥ (1 : uint64) <<< 16 then 16 else 0
  let x := if x ≥ (1 : uint64) <<< 16 then x >>> 16 else x
  let n := if x ≥ (1 : uint64) <<< 8 then n + 8 else n
  let x := if x ≥ (1 : uint64) <<< 8 then x >>> 8 else x
  n + (tab len8tab (x.setWidth 8)).zeroExtend 64
theorem Len64NoHighHalf_spec (x : uint64) : Len64NoHighHalf x = len x := by
  dsimp only [Len64NoHighHalf]; rw [len8tab_eq_fn]
  unroll_spec; unfold len8tabFn; bv_decide
