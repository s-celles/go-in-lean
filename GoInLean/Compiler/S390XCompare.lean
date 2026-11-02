import Std.Tactic.BVDecide
/-!
# s390x: narrowing 64-bit compares of extended values to 32 bits (finding S390X-CMPU-SIGNEXT)

`S390X.rules` (go1.25.5 .. master `babb75be`, "Convert 64-bit comparisons to 32-bit comparisons"):

    (CM(P|P|PU|PU)const x:(MOV(H|HZ|H|HZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])
    (CM(P|P|PU|PU)const x:(MOV(B|BZ|B|BZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])

The alternatives expand in lockstep: (P,H), (P,HZ), (PU,H), (PU,HZ) and the same for bytes.
`CMPUconst x [c]` compares the 64-bit register with the zero-extended 32-bit immediate;
`CMPWUconst x [c]` compares the low 32 bits. For a sign-extended negative value the 64-bit
register is ≥ 2^64 - 2^15, larger than any immediate, but its low half (≥ 2^32 - 2^15) can be
below or equal to an immediate close to 2^32. Reachable since go1.26 (register ABI on s390x:
the `MOVBreg` of an argument is no longer folded into a sign-extending load).

A comparison is modelled by its two outcomes (unsigned less-than, equality), which determine
every condition code (`Less`, `LessOrEqual`, `Equal`, …).
-/
namespace Go.Compiler.S390XCompare

def sextH (h : BitVec 16) : BitVec 64 := h.signExtend 64
def zextH (h : BitVec 16) : BitVec 64 := h.setWidth 64
def sextB (b : BitVec 8) : BitVec 64 := b.signExtend 64
def zextB (b : BitVec 8) : BitVec 64 := b.setWidth 64

/-- `CMPUconst x [c]` / `CMPWUconst x [c]` (immediate zero-extended). -/
def cmpU (x : BitVec 64) (c : BitVec 32) : Bool × Bool := (x.ult (c.setWidth 64), x == c.setWidth 64)
def cmpWU (x : BitVec 64) (c : BitVec 32) : Bool × Bool := ((x.setWidth 32).ult c, x.setWidth 32 == c)
/-- `CMPconst x [c]` / `CMPWconst x [c]` (immediate sign-extended). -/
def cmpS (x : BitVec 64) (c : BitVec 32) : Bool × Bool := (x.slt (c.signExtend 64), x == c.signExtend 64)
def cmpWS (x : BitVec 64) (c : BitVec 32) : Bool × Bool := ((x.setWidth 32).slt c, x.setWidth 32 == c)

/-- The faulty instance on bytes: `uint64(int8(-128)) < 0xFFFFFFFF` is false, the 32-bit compare says true. -/
theorem cmpu_movbreg_refuted : cmpU (sextB 0x80) 0xFFFFFFFF = (false, false) ∧
    cmpWU (sextB 0x80) 0xFFFFFFFF = (true, false) := by decide

theorem cmpu_movhreg_refuted : cmpU (sextH 0xFFFE) 0xFFFFFFFE = (false, false) ∧
    cmpWU (sextH 0xFFFE) 0xFFFFFFFE = (false, true) := by decide

/-- Fix: the unsigned narrowing of a sign-extended value is sound when the immediate is below 2^31. -/
theorem cmpu_movhreg_fixed (h : BitVec 16) (c : BitVec 32) (hc : c.msb = false) :
    cmpU (sextH h) c = cmpWU (sextH h) c := by
  unfold cmpU cmpWU sextH; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})

theorem cmpu_movbreg_fixed (b : BitVec 8) (c : BitVec 32) (hc : c.msb = false) :
    cmpU (sextB b) c = cmpWU (sextB b) c := by
  unfold cmpU cmpWU sextB; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})

/-- The other three instances of each rule are sound for every immediate. -/
theorem cmp_movhreg_sound (h : BitVec 16) (c : BitVec 32) : cmpS (sextH h) c = cmpWS (sextH h) c := by
  unfold cmpS cmpWS sextH; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmp_movhzreg_sound (h : BitVec 16) (c : BitVec 32) : cmpS (zextH h) c = cmpWS (zextH h) c := by
  unfold cmpS cmpWS zextH; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmpu_movhzreg_sound (h : BitVec 16) (c : BitVec 32) : cmpU (zextH h) c = cmpWU (zextH h) c := by
  unfold cmpU cmpWU zextH; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmp_movbreg_sound (b : BitVec 8) (c : BitVec 32) : cmpS (sextB b) c = cmpWS (sextB b) c := by
  unfold cmpS cmpWS sextB; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmp_movbzreg_sound (b : BitVec 8) (c : BitVec 32) : cmpS (zextB b) c = cmpWS (zextB b) c := by
  unfold cmpS cmpWS zextB; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmpu_movbzreg_sound (b : BitVec 8) (c : BitVec 32) : cmpU (zextB b) c = cmpWU (zextB b) c := by
  unfold cmpU cmpWU zextB; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})

/-- The word rule `(CM(P|PU)const (MOV(W|WZ)reg x) [c])` pairs signed with sign-extension and
unsigned with zero-extension, and is sound. -/
theorem cmp_movwreg_sound (w : BitVec 32) (c : BitVec 32) :
    cmpS (w.signExtend 64) c = cmpWS (w.signExtend 64) c := by
  unfold cmpS cmpWS; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})
theorem cmpu_movwzreg_sound (w : BitVec 32) (c : BitVec 32) :
    cmpU (w.setWidth 64) c = cmpWU (w.setWidth 64) c := by
  unfold cmpU cmpWU; simp only [Prod.mk.injEq]; bv_decide (config := {timeout := 120})

end Go.Compiler.S390XCompare
