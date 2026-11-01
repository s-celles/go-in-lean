import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
open Go Go.Bits
/-- MUTANT: rotation count masked with 31 instead of 63. The spec is stated
against the correct model `RotateLeft64` (proved equal to `BitVec.rotateLeft`). -/
def RotateLeft64OffByOne (x : uint64) (k : int) : uint64 :=
  let s : uint := k &&& (32 - 1)
  (x <<< s) ||| (x >>> (64 - s))
theorem RotateLeft64OffByOne_spec (x : uint64) (k : int) :
    RotateLeft64OffByOne x k = RotateLeft64 x k := by
  dsimp only [RotateLeft64OffByOne, RotateLeft64]; bv_decide
