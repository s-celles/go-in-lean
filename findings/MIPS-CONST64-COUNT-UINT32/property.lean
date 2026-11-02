import Std.Tactic.BVDecide
/-!
# MIPS (32-bit): constant 64-bit shift counts truncated to 32 bits (finding MIPS-CONST64-COUNT-UINT32)

`MIPS.rules:58-79` (go1.12 .. master `babb75be`), e.g.

    (Rsh8x64 x (Const64 [c])) && uint32(c) < 8  => (SRAconst (SLLconst <typ.UInt32> x [24]) [int32(c+24)])
    (Rsh8x64 x (Const64 [c])) && uint32(c) >= 8 => (SRAconst (SLLconst <typ.UInt32> x [24]) [31])

test `uint32(c)`; `ARM.rules` and `386.rules` test `uint64(c)`. The lowering assumes a 64-bit
constant count was split by `dec64` first, but the generic shift-merging rule
`(Rsh8x64 (Rsh8x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh8x64 x (Const64 <t> [c+d]))`
runs again in `late_opt`, after decomposition, and can produce a count ≥ 2^32:
`(x >> 7) >> (uint64(y) | 0xFFFFFFFF)` becomes `x >> 4294967302`, lowered as `x >> 6`.
-/
namespace Go.Compiler.MIPSConstCount

/-- The 32-bit register value produced for `Rsh8x64 x (Const64 [c])` by the rule pair, with the
count test done on `uint32(c)` (current) or `uint64(c)` (fix). `x` is the int8 in the low byte. -/
def lowered (wide : Bool) (x : BitVec 32) (c : BitVec 64) : BitVec 32 :=
  let k : BitVec 64 := if wide then c else (c.setWidth 32).setWidth 64
  if k < 8 then (x <<< 24).sshiftRight' ((c.setWidth 32) + 24) else (x <<< 24).sshiftRight' (31 : BitVec 32)

/-- Go: `int8 >> uint64`. -/
def spec (x : BitVec 8) (c : BitVec 64) : BitVec 8 := x.sshiftRight' c

/-- The count of the reproducer: `7 + 0xFFFFFFFF`, no unsigned overflow. -/
theorem merged_count : (7 : BitVec 64) + 0xFFFFFFFF = 4294967302 := by decide

theorem rsh8x64_refuted :
    (lowered false 0x7F 4294967302).setWidth 8 = 1 ∧ spec 0x7F 4294967302 = 0 := by decide

theorem rsh8x64_fixed (x : BitVec 32) (c : BitVec 64) :
    (lowered true x c).setWidth 8 = spec (x.setWidth 8) c := by
  unfold lowered spec; bv_decide (config := {timeout := 120})

/-- The current rules are sound whenever the count fits in 32 bits. -/
theorem rsh8x64_ok_below_2_32 (x : BitVec 32) (c : BitVec 64) (h : c < 0x100000000) :
    (lowered false x c).setWidth 8 = spec (x.setWidth 8) c := by
  unfold lowered spec; bv_decide (config := {timeout := 120})

end Go.Compiler.MIPSConstCount
