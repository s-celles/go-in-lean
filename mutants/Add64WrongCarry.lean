import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
open Go Go.Bits
/-- MUTANT: carry formula drops the `(x|y) &^ sum` term. -/
def Add64WrongCarry (x y carry : uint64) : uint64 × uint64 :=
  let sum := x + y + carry
  let carryOut := (x &&& y) >>> 63
  (sum, carryOut)
theorem Add64WrongCarry_spec (x y carry : uint64) (hc : carry = 0 ∨ carry = 1) :
    ((Add64WrongCarry x y carry).2.zeroExtend 128 <<< 64) ||| (Add64WrongCarry x y carry).1.zeroExtend 128
      = x.zeroExtend 128 + y.zeroExtend 128 + carry.zeroExtend 128 := by
  dsimp only [Add64WrongCarry]; bv_decide
