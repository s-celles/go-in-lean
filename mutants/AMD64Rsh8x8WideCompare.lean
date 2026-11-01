import Std.Tactic.BVDecide
import GoInLean.Compiler.AMD64
open Go.Compiler
/-- MUTANT (same class as golang/go#79886, on AMD64): the unbounded `Rsh8x8` lowering uses
`CMPQconst` (64-bit compare) instead of `CMPBconst` on an 8-bit shift amount whose register
has garbage above bit 8. -/
theorem Rsh8x8_wideCompare (rx ry : BitVec 64) :
    let x : BitVec 8 := rx.setWidth 8
    let y : BitVec 8 := ry.setWidth 8
    (X86.sarb rx (X86.orl ry (X86.notl (X86.sbblCarrymask (X86.cmpCarry 64 ry 8))))).setWidth 8
      = x.sshiftRight' y := by
  intro x y
  simp only [x, y, X86.sarb, X86.orl, X86.notl, X86.low, X86.put, X86.cmpCarry, X86.sbblCarrymask]
  bv_decide
