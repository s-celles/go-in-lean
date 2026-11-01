/-!
# ARM64 machine operations used by the shift lowering rules

Arm Architecture Reference Manual, A64: LSLV/LSRV/ASRV ("the remaining
bits of the shift amount are ignored": the amount is taken modulo the
register width, i.e. `& 63` for X registers); MOVBU/MOVHU/MOVWU zero-extend,
MOVB/MOVH/MOVW sign-extend the low 8/16/32 bits. A register is a `BitVec 64`.
-/
namespace Go.Compiler.Arm

def sll (a b : BitVec 64) : BitVec 64 := a <<< (b &&& 63)
def srl (a b : BitVec 64) : BitVec 64 := a >>> (b &&& 63)
def sra (a b : BitVec 64) : BitVec 64 := a.sshiftRight' (b &&& 63)
def zext (n : Nat) (a : BitVec 64) : BitVec 64 := (a.setWidth n).setWidth 64
def sext (n : Nat) (a : BitVec 64) : BitVec 64 := (a.setWidth n).signExtend 64

end Go.Compiler.Arm
