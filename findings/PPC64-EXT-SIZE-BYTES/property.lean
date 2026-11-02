import Std.Tactic.BVDecide
/-!
# ppc64: sign/zero-extension elimination after 32-bit right shifts (finding PPC64-EXT-SIZE-BYTES)

`PPC64.rules` (go1.21 .. master `babb75be`; `sizeof(x.Type) <= 16` already in go1.19):

    (MOV(WZ|W)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 32 => (S(R|RA)Wconst [c] x)
    (MOV(HZ|H)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 16 => (S(R|RA)Wconst [c] x)
    (MOV(BZ|B)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() == 8 => (S(R|RA)Wconst [c] x)

`Type.Size()` is in bytes, so the conditions are always true (W, H) or true exactly for 64-bit
values (B). The H and B rules drop the 16/8-bit extension of a 32-bit shift whose result does
not fit: `int32(int16(x >> 1))` with `x = -2^31` gives `-2^30` instead of 0. The W rule is
harmless (SRW/SRAW already extend their 32-bit result). Even with the intended `Size() <= 2`,
the type would not guarantee an extended register, so the fix removes the H and B rules; the
pattern-based rules `(MOV(H|W)reg (SRAWconst [c] (MOVHreg x)))` etc. remain and are sound.

Model: 64-bit registers; `SRAWconst [c] x` sign-extends the 32-bit result, `SRWconst` zero-extends.
-/
namespace Go.Compiler.PPC64ExtShift

def sraw (c : Nat) (x : BitVec 64) : BitVec 64 := ((x.setWidth 32).sshiftRight c).signExtend 64
def srw (c : Nat) (x : BitVec 64) : BitVec 64 := ((x.setWidth 32) >>> c).setWidth 64
def movhreg (r : BitVec 64) : BitVec 64 := (r.setWidth 16).signExtend 64
def movhzreg (r : BitVec 64) : BitVec 64 := (r.setWidth 16).setWidth 64
def movbreg (r : BitVec 64) : BitVec 64 := (r.setWidth 8).signExtend 64
def movbzreg (r : BitVec 64) : BitVec 64 := (r.setWidth 8).setWidth 64
def movwreg (r : BitVec 64) : BitVec 64 := (r.setWidth 32).signExtend 64
def movwzreg (r : BitVec 64) : BitVec 64 := (r.setWidth 32).setWidth 64

/-- `int32(int16(x >> 1))`, `x = -2^31`: the rule's result `-2^30`, Go's 0. -/
theorem movhreg_sraw_refuted : movhreg (sraw 1 0x80000000) = 0 ∧ sraw 1 0x80000000 ≠ 0 := by decide
theorem movhzreg_srw_refuted : movhzreg (srw 1 0x80000000) = 0 ∧ srw 1 0x80000000 ≠ 0 := by decide
theorem movbreg_sraw_refuted : movbreg (sraw 1 0x80000000) = 0 ∧ sraw 1 0x80000000 ≠ 0 := by decide
theorem movbzreg_srw_refuted : movbzreg (srw 1 0x80000000) = 0 ∧ srw 1 0x80000000 ≠ 0 := by decide

/-- The W rule is sound for every operand and count < 32. -/
theorem movwreg_sraw_sound (x c : BitVec 64) (_hc : c < 32) :
    movwreg (((x.setWidth 32).sshiftRight' (c.setWidth 32)).signExtend 64) =
      ((x.setWidth 32).sshiftRight' (c.setWidth 32)).signExtend 64 := by
  unfold movwreg; bv_decide (config := {timeout := 120})
theorem movwzreg_srw_sound (x c : BitVec 64) (_hc : c < 32) :
    movwzreg (((x.setWidth 32) >>> (c.setWidth 32)).setWidth 64) =
      ((x.setWidth 32) >>> (c.setWidth 32)).setWidth 64 := by
  unfold movwzreg; bv_decide (config := {timeout := 120})

/-- The remaining pattern-based rules are sound (operand explicitly extended first). -/
theorem movhreg_sraw_movhreg_sound (x : BitVec 64) (c : BitVec 64) (hc : c < 32) :
    movhreg ((((movhreg x).setWidth 32).sshiftRight' (c.setWidth 32)).signExtend 64) =
      (((movhreg x).setWidth 32).sshiftRight' (c.setWidth 32)).signExtend 64 := by
  unfold movhreg; bv_decide (config := {timeout := 120})
theorem movhzreg_srw_movhzreg_sound (x : BitVec 64) (c : BitVec 64) (hc : c < 32) :
    movhzreg ((((movhzreg x).setWidth 32) >>> (c.setWidth 32)).setWidth 64) =
      (((movhzreg x).setWidth 32) >>> (c.setWidth 32)).setWidth 64 := by
  unfold movhzreg; bv_decide (config := {timeout := 120})

/-- The count-based rule `(MOVHreg (SRAWconst [c] x)) && c >= 16` is sound. -/
theorem movhreg_sraw_c16_sound (x c : BitVec 64) (h1 : 16 ≤ c) (h2 : c < 32) :
    movhreg ((((x.setWidth 32).sshiftRight' (c.setWidth 32))).signExtend 64) =
      ((x.setWidth 32).sshiftRight' (c.setWidth 32)).signExtend 64 := by
  unfold movhreg; bv_decide (config := {timeout := 120})

end Go.Compiler.PPC64ExtShift
