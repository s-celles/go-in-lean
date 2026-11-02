import Std.Tactic.BVDecide
/-!
# riscv64: a 64-bit shift typed as 8/16 bits meets a type-trusting fold (finding RISCV64-SLLI-NARROW-TYPE)

`RISCV64.rules` (go1.26.10, go1.27.3, master `babb75be`):

    (SRAI <t> [x] (MOVBreg y)) && x >=  8 => (SRAI  [63] (SLLI <t> [56] y))      -- since go1.21 or earlier
    (SRAI <t> [x] (MOVHreg y)) && x >= 16 => (SRAI  [63] (SLLI <t> [48] y))
    (SLLI <t> [c] (ADD x x)) && c >= t.Size() * 8 - 1 => (MOVDconst [0])        -- new in go1.26

The first rule moves the byte to the top of the 64-bit register and reads bit 63, but types the
`SLLI` with the 8-bit result type `t`. The fold trusts `t`: modulo 2^8, `(x+x) << c` is 0 once
`c ≥ 7`, but in 64 bits it is not, and the outer `SRAI [63]` reads bit 63. Since the lowering
also turns `x - (-x)` into `ADD x x` (`(SUB x (NEG y)) => (ADD x y)`), `int8(x - (-x)) >> 8`
compiles to the constant 0. Fix: type the `SLLI` as `Int64`; then `(SLLI [c] (ADD x x)) => (SLLI [c+1] x)`
(c = 56 < 63) applies instead, which is sound in 64 bits.
-/
namespace Go.Compiler.RISCV64Narrow

def slli (c : Nat) (x : BitVec 64) : BitVec 64 := x <<< c
def srai (c : Nat) (x : BitVec 64) : BitVec 64 := x.sshiftRight c
def movbreg (y : BitVec 64) : BitVec 64 := (y.setWidth 8).signExtend 64

/-- The fold is only true of the low byte (what an 8-bit type promises)… -/
theorem fold_low_byte (x : BitVec 64) : (slli 56 (x + x)).setWidth 8 = 0 := by
  unfold slli; bv_decide (config := {timeout := 120})

/-- …not of the 64-bit register that the outer `SRAI [63]` reads. -/
theorem fold_full_refuted : slli 56 (1 + 1) ≠ 0 := by decide

/-- The lowering rule itself is sound in 64 bits for every count it accepts (`8 ≤ x ≤ 63`). -/
theorem srai_movbreg_sound (y x : BitVec 64) (h1 : 8 ≤ x) (h2 : x ≤ 63) :
    (movbreg y).sshiftRight' x = srai 63 (slli 56 y) := by
  unfold srai slli movbreg; bv_decide (config := {timeout := 120})

/-- Composite with the go1.26 fold: the compiled result is 0, the Go result is -1 (x = -1). -/
theorem composite_refuted :
    srai 63 0 ≠ srai 63 (slli 56 ((-1 : BitVec 64) + (-1))) := by decide

/-- Fixed path: `SLLI <Int64> [56] (ADD x x)` becomes `SLLI [57] x`, which is equal in 64 bits… -/
theorem fixed_fold_sound (x : BitVec 64) : slli 56 (x + x) = slli 57 x := by
  unfold slli; bv_decide (config := {timeout := 120})

/-- …and the whole lowering of `int8(x + x) >> k`, `8 ≤ k`, matches Go semantics. -/
theorem fixed_end_to_end (x : BitVec 64) :
    (srai 63 (slli 57 x)).setWidth 8 =
      (if ((x + x).setWidth 8).msb then (-1 : BitVec 8) else 0) := by
  unfold srai slli; bv_decide (config := {timeout := 120})

end Go.Compiler.RISCV64Narrow
