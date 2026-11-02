import Std.Tactic.BVDecide
/-!
# MIPS (32-bit) lowering of signed 8-bit variable shifts (finding MIPS-RSH8-SIGNEXT16)

`MIPS.rules:116-118` (go1.27.3 and master `babb75be`, unchanged since go1.8):

    (Rsh8x32 x y) => (SRA (SignExt16to32 x) ( CMOVZ <typ.UInt32> y (MOVWconst [31]) (SGTUconst [32] y)))
    (Rsh8x16 x y) => (SRA (SignExt16to32 x) ( CMOVZ ... (ZeroExt16to32 y) ...))
    (Rsh8x8 x y)  => (SRA (SignExt16to32 x) ( CMOVZ ... (ZeroExt8to32 y) ...))

An 8-bit value lives in a 32-bit register whose upper 24 bits are unspecified (e.g. the raw
result of `MUL` or `ADDU`). The rules sign-extend from bit 15 instead of bit 7, so bits 8-15
leak into the arithmetic shift. Every other signed 8-bit rule in the file uses `SignExt8to32`,
and `MIPS64.rules` uses `SignExt8to64`.

Model: registers are `BitVec 32` with arbitrary upper bits; the Go value is the low byte.
* `rsh8x32_refuted`: kernel-checked witness (register `0xF88F`, i.e. int8 `-113` with garbage
  `0xF8` above it, count 8): the rule yields `-8`, Go semantics `-1`. This is the input of the
  Go reproducer (`127 * -15` leaves `0xFFFFF88F` in the register).
* `rsh8x{32,16,8}_fixed`: with `SignExt8to32` the rules are sound for every register and count.
* `rsh8x32_ok_if_extended`: the current rule is sound when the register is already sign-extended
  from bit 7 (values loaded with `MOVB`), which is why ordinary code rarely shows the bug.
-/
namespace Go.Compiler.MIPSShift8

/-- `SignExt8to32` / `SignExt16to32` on a 32-bit register (`MOVBreg` / `MOVHreg`). -/
def sext8 (r : BitVec 32) : BitVec 32 := (r.setWidth 8).signExtend 32
def sext16 (r : BitVec 32) : BitVec 32 := (r.setWidth 16).signExtend 32

/-- `CMOVZ y (MOVWconst [31]) (SGTUconst [32] y)`: `y` if `32 >u y`, else 31. -/
def clamp (y : BitVec 32) : BitVec 32 := if y < 32 then y else 31

/-- `SRA v c`: arithmetic right shift by the low 5 bits of the count register. -/
def sra (v c : BitVec 32) : BitVec 32 := v.sshiftRight' (c &&& 31)

/-- Go: `int8 >> uint32` (sign fill once the count reaches 8). -/
def spec (a : BitVec 8) (y : BitVec 32) : BitVec 8 :=
  if y < 8 then a.sshiftRight' (y.setWidth 8) else (if a.msb then -1 else 0)

/-- The lowering as written (`SignExt16to32`) and as fixed (`SignExt8to32`). -/
def rule (ext : BitVec 32 → BitVec 32) (x y : BitVec 32) : BitVec 8 :=
  (sra (ext x) (clamp y)).setWidth 8

/-- `spec` agrees with Lean's `sshiftRight` by the count's value (sanity check of the spec). -/
theorem spec_eq (a : BitVec 8) (y : BitVec 32) : spec a y = a.sshiftRight' y := by
  unfold spec; bv_decide (config := {timeout := 120})

theorem rsh8x32_refuted : rule sext16 0x0000F88F 8 = 0xF8 ∧ spec 0x8F 8 = 0xFF := by decide

theorem rsh8x32_unsound :
    ¬ ∀ x y : BitVec 32, rule sext16 x y = spec (x.setWidth 8) y := by
  intro h; have := h 0x0000F88F 8; revert this; decide

theorem rsh8x32_fixed (x y : BitVec 32) : rule sext8 x y = spec (x.setWidth 8) y := by
  unfold rule spec sra clamp sext8; bv_decide (config := {timeout := 120})

theorem rsh8x16_fixed (x : BitVec 32) (y : BitVec 16) :
    rule sext8 x (y.setWidth 32) = spec (x.setWidth 8) (y.setWidth 32) := rsh8x32_fixed x _

theorem rsh8x8_fixed (x : BitVec 32) (y : BitVec 8) :
    rule sext8 x (y.setWidth 32) = spec (x.setWidth 8) (y.setWidth 32) := rsh8x32_fixed x _

theorem rsh8x32_ok_if_extended (x y : BitVec 32) (h : x = sext8 x) :
    rule sext16 x y = spec (x.setWidth 8) y := by
  unfold rule spec sra clamp sext8 sext16 at *; bv_decide (config := {timeout := 120})

/-- The 16-bit rules (`Rsh16x*`, `SignExt16to32`) are sound: the defect is specific to 8 bits. -/
theorem rsh16x32_sound (x y : BitVec 32) :
    (sra (sext16 x) (clamp y)).setWidth 16 = (x.setWidth 16).sshiftRight' y := by
  unfold sra clamp sext16; bv_decide (config := {timeout := 120})

end Go.Compiler.MIPSShift8
