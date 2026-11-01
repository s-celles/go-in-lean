/-!
# AMD64 machine operations used by the shift lowering rules

Intel SDM Vol. 2, SAL/SAR/SHL/SHR: the count is masked to 6 bits for 64-bit
operands (REX.W) and to 5 bits otherwise — also for 8- and 16-bit operands,
so `SHRW` by 20 shifts a 16-bit value by 20 (result 0). 32-bit operations
zero the upper 32 bits of the destination; 8/16-bit operations leave them
unchanged (irrelevant here: only the low bits are read). `SBBxcarrymask`
(Go SSA op) is `SBB r, r`: all ones (of the operand width) if CF else 0.
`CMPxconst y [k]` sets CF iff the low 64/32/16/8 bits of `y` are below `k`
(unsigned). A register is a `BitVec 64`.
-/
namespace Go.Compiler.X86

def low (n : Nat) (a : BitVec 64) : BitVec n := a.setWidth n
/-- Write an `n`-bit result into register `a`: 32-bit writes zero-extend, 8/16 keep the top. -/
def put (n : Nat) (a : BitVec 64) (r : BitVec n) : BitVec 64 :=
  if n = 32 then r.setWidth 64 else
  if n = 64 then r.setWidth 64 else
  (a &&& ~~~((BitVec.allOnes n).setWidth 64)) ||| r.setWidth 64

def shlq (a c : BitVec 64) : BitVec 64 := a <<< (c &&& 63)
def shrq (a c : BitVec 64) : BitVec 64 := a >>> (c &&& 63)
def sarq (a c : BitVec 64) : BitVec 64 := a.sshiftRight' (c &&& 63)
def shll (a c : BitVec 64) : BitVec 64 := put 32 a (low 32 a <<< (low 32 c &&& 31))
def shrl (a c : BitVec 64) : BitVec 64 := put 32 a (low 32 a >>> (low 32 c &&& 31))
def sarl (a c : BitVec 64) : BitVec 64 := put 32 a ((low 32 a).sshiftRight' (low 32 c &&& 31))
def shrw (a c : BitVec 64) : BitVec 64 := put 16 a (low 16 a >>> (low 16 c &&& 31))
def sarw (a c : BitVec 64) : BitVec 64 := put 16 a ((low 16 a).sshiftRight' (low 16 c &&& 31))
def shrb (a c : BitVec 64) : BitVec 64 := put 8 a (low 8 a >>> (low 8 c &&& 31))
def sarb (a c : BitVec 64) : BitVec 64 := put 8 a ((low 8 a).sshiftRight' (low 8 c &&& 31))
def andq (a b : BitVec 64) : BitVec 64 := a &&& b
def andl (a b : BitVec 64) : BitVec 64 := put 32 a (low 32 a &&& low 32 b)
def orq (a b : BitVec 64) : BitVec 64 := a ||| b
def orl (a b : BitVec 64) : BitVec 64 := put 32 a (low 32 a ||| low 32 b)
def notq (a : BitVec 64) : BitVec 64 := ~~~a
def notl (a : BitVec 64) : BitVec 64 := put 32 a (~~~(low 32 a))
/-- Carry flag of `CMP{n}const y [k]`: unsigned `low n y < k`. -/
def cmpCarry (n : Nat) (y : BitVec 64) (k : Nat) : Bool := decide (low n y < BitVec.ofNat n k)
def sbbqCarrymask (cf : Bool) : BitVec 64 := if cf then BitVec.allOnes 64 else 0
def sbblCarrymask (cf : Bool) : BitVec 64 := if cf then (BitVec.allOnes 32).setWidth 64 else 0

end Go.Compiler.X86
