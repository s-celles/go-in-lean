import Std.Tactic.BVDecide
/-!
# ppc64 Power10: `ReverseBytes16` result typed as 64-bit uint (finding PPC64-POWER10-BSWAP16-BCE)

The Power10 `ReverseBytes16` intrinsic builds `OpBswap16` with result type `TUINT` (64-bit
unsigned), while the loong64 and riscv64 intrinsics use `TUINT16`. The value really holds a
16-bit byte reversal, but the SSA type tells the prove / knownbits passes it is a full 64-bit
unsigned. A consumer `^int16(v)` then gets a sign fact that is false at the true width, and in
go1.27 prove uses it to fold a branch and fold a comparison to the wrong value.

This models the type-level root cause: the set of signed values of `^int16(bswap16 x)` is all of
`int16`, so no `< 0` / `>= 0` fact holds; but if the producer is trusted to be a non-negative
64-bit quantity whose `int16` truncation keeps its sign, a false fact follows.
-/
namespace Go.Compiler.PPC64Bswap16

/-- Byte reversal of a 16-bit value (what BRH computes on the low half). -/
def bswap16 (x : BitVec 16) : BitVec 16 := (x.extractLsb' 0 8 ++ x.extractLsb' 8 8)

/-- `^int16(bswap16 x)` as a signed 16-bit value. -/
def notRev (x : BitVec 16) : BitVec 16 := ~~~ bswap16 x

/-- Honest range: `notRev` takes both signs, so neither `< 0` nor `>= 0` is an invariant. -/
theorem notRev_neg_witness : (notRev 0x0004).slt 0 = true := by decide
theorem notRev_nonneg_witness : (notRev 0xFCFF).slt 0 = false := by decide

/-- The false fact the mistyping enables: "treated as a non-negative 64-bit value, its low-16
truncation is non-negative". `bswap16` zero-extended to 64 bits is always `< 2^16`, hence its
MSB-as-64 is 0 (non-negative), yet `^` of its int16 can be negative. The contradiction is that a
64-bit-non-negative producer does NOT imply `^int16(.) >= 0`. -/
theorem mistyping_unsound :
    ¬ (∀ x : BitVec 16, (notRev x).msb = false) := by
  intro h; have := h 0x0004; revert this; decide

/-- With the correct 16-bit type, no such 64-bit non-negativity is claimed; the value is just a
signed int16 and both branches of `if r < 0` are reachable (so the check must stay). -/
theorem both_branches_reachable :
    (∃ x : BitVec 16, (notRev x).slt 0 = true) ∧ (∃ x : BitVec 16, (notRev x).slt 0 = false) := by
  refine ⟨⟨0x0004, ?_⟩, ⟨0xFCFF, ?_⟩⟩ <;> decide

end Go.Compiler.PPC64Bswap16
