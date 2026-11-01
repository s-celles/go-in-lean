import Std.Tactic.BVDecide
import GoInLean.Compiler.ARM64
open Go.Compiler
/-- MUTANT (class of golang/go#79886): the unbounded `Lsh64x32` lowering compares the raw
32-bit shift-amount register against 64 instead of `ZeroExt32to64 y`. With garbage in the upper
32 bits of `y`, the compare says "≥ 64" and the result is 0 where Go requires `x << y`. -/
theorem Lsh64x32_noZeroExt (rx ry : BitVec 64) :
    let x : BitVec 64 := rx
    let y : BitVec 32 := ry.setWidth 32
    ((if ry < (64 : BitVec 64) then Arm.sll rx ry else (0 : BitVec 64))).setWidth 64 = x <<< y := by
  intro x y
  simp only [x, y, Arm.sll]
  bv_decide
