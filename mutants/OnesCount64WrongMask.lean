import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
import GoInLean.Properties.Bits
open Go Go.Bits Go.BitSpec Go.Bits.Properties
set_option maxRecDepth 16384
/-- MUTANT: second SWAR mask is 0x3333…3332 instead of 0x3333…3333. -/
def OnesCount64WrongMask (x : uint64) : int :=
  let m0 : uint64 := 0x5555555555555555
  let m1 : uint64 := 0x3333333333333332
  let m2 : uint64 := 0x0f0f0f0f0f0f0f0f
  let x := ((x >>> 1) &&& m0) + (x &&& m0)
  let x := ((x >>> 2) &&& m1) + (x &&& m1)
  let x := ((x >>> 4) + x) &&& m2
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x + (x >>> 32)
  x &&& (((1 : uint64) <<< 7) - 1)
theorem OnesCount64WrongMask_spec (x : uint64) : OnesCount64WrongMask x = popcount x := by
  dsimp only [OnesCount64WrongMask]; unroll_spec; bv_decide
