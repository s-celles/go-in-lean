import Std.Tactic.BVDecide
import GoInLean.Compiler.Rotates
open Go.Compiler Go.Compiler.Rotates
/-- MUTANT: ARM64.rules:70 without `ZeroExt8to64` before `SRL`: the garbage bits 8..15 of the
`x` register are shifted into the low byte. -/
theorem RotateLeft8_noZeroExt (rx ry : BitVec 64) :
    ((Arm.sll rx (ry &&& 7)) ||| (Arm.srl rx ((-ry) &&& 7))).setWidth 8 = goRotl 8 rx ry := by
  unfold_rot; bv_decide
