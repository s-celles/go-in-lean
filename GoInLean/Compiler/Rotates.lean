import Std.Tactic.BVDecide
import GoInLean.Compiler.ARM64
import GoInLean.Compiler.AMD64
/-!
# Rotate lowering rules (ARM64.rules:69-74, 1025-1026; AMD64.rules:566-569, 824-844)

Generic semantics (genericOps.go:256-259): "RotateLeftX instructions rotate the X bits of
arg[0] to the left by the low lg_2(X) bits of arg[1], interpreted as an unsigned value."
Registers are `BitVec 64` with arbitrary bits above the Go type's width, as in the shift files.

`rotl x k` is the shift-based rotation for `k < w`; `rotl_eq_rotateLeft_8` ties it to core
`BitVec.rotateLeft` (kernel `decide`, all 8-bit inputs).
-/
namespace Go.Compiler.Rotates
open Go.Compiler

/-- Left rotation by `k` (`k < w`), via shifts. -/
def rotl {w : Nat} (x k : BitVec w) : BitVec w := (x <<< k) ||| (x >>> (BitVec.ofNat w w - k))
def rotr {w : Nat} (x k : BitVec w) : BitVec w := (x >>> k) ||| (x <<< (BitVec.ofNat w w - k))

theorem rotl_eq_rotateLeft_8 : ∀ x k : BitVec 8, k < 8 → rotl x k = x.rotateLeft k.toNat := by
  decide

/-- Go semantics of `RotateLeftN x y` on registers. -/
def goRotl (n : Nat) (rx ry : BitVec 64) : BitVec n :=
  rotl (rx.setWidth n) (ry.setWidth n &&& BitVec.ofNat n (n - 1))

-- ARM64 machine ops (Arm ARM: RORV uses amount mod datasize; W forms zero the top half)
def ror (a b : BitVec 64) : BitVec 64 := rotr a (b &&& 63)
def rorw (a b : BitVec 64) : BitVec 64 := (rotr (a.setWidth 32) (b.setWidth 32 &&& 31)).setWidth 64
def orshiftLL (k : Nat) (a b : BitVec 64) : BitVec 64 := a ||| (b <<< k)

-- AMD64 machine ops (Intel SDM ROL/ROR: count masked to 5 bits (6 with REX.W), then taken
-- modulo the operand size for 8/16-bit operands; 32-bit ops zero the top half).
def rolq (a c : BitVec 64) : BitVec 64 := rotl a (c &&& 63)
def roll (a c : BitVec 64) : BitVec 64 := (rotl (a.setWidth 32) (c.setWidth 32 &&& 31)).setWidth 64
def rolw (a c : BitVec 64) : BitVec 64 := (rotl (a.setWidth 16) (c.setWidth 16 &&& 31 &&& 15)).setWidth 64
def rolb (a c : BitVec 64) : BitVec 64 := (rotl (a.setWidth 8) (c.setWidth 8 &&& 31 &&& 7)).setWidth 64
def rorq (a c : BitVec 64) : BitVec 64 := rotr a (c &&& 63)
def rorl (a c : BitVec 64) : BitVec 64 := (rotr (a.setWidth 32) (c.setWidth 32 &&& 31)).setWidth 64
def rorw' (a c : BitVec 64) : BitVec 64 := (rotr (a.setWidth 16) (c.setWidth 16 &&& 31 &&& 15)).setWidth 64
def rorb (a c : BitVec 64) : BitVec 64 := (rotr (a.setWidth 8) (c.setWidth 8 &&& 31 &&& 7)).setWidth 64
def negq (a : BitVec 64) : BitVec 64 := -a
def negl (a : BitVec 64) : BitVec 64 := (-(a.setWidth 32)).setWidth 64
/-- `ROLxconst [k]`: the immediate is masked like a register count. -/
def rolqc (k : BitVec 64) (a : BitVec 64) : BitVec 64 := rolq a k

macro "unfold_rot" : tactic => `(tactic| simp only [goRotl, rotl, rotr, ror, rorw, orshiftLL,
  rolq, roll, rolw, rolb, rorq, rorl, rorw', rorb, negq, negl, rolqc, Arm.sll, Arm.srl, Arm.zext])

-- ---------------------------------------------------------------- ARM64

/-- ARM64.rules:70 `(RotateLeft8 <t> x y) => (OR (SLL x (ANDconst [7] y)) (SRL (ZeroExt8to64 x) (ANDconst [7] (NEG y))))` -/
theorem arm64_rotl8 (rx ry : BitVec 64) :
    ((Arm.sll rx (ry &&& 7)) ||| (Arm.srl (Arm.zext 8 rx) ((-ry) &&& 7))).setWidth 8 = goRotl 8 rx ry := by
  unfold_rot; bv_decide
/-- ARM64.rules:72 `(RotateLeft16 <t> x y) => (RORW (ORshiftLL (ZeroExt16to32 x) (ZeroExt16to32 x) [16]) (NEG y))` -/
theorem arm64_rotl16 (rx ry : BitVec 64) :
    (rorw (orshiftLL 16 (Arm.zext 16 rx) (Arm.zext 16 rx)) (-ry)).setWidth 16 = goRotl 16 rx ry := by
  unfold_rot; bv_decide
/-- ARM64.rules:73 `(RotateLeft32 x y) => (RORW x (NEG y))` -/
theorem arm64_rotl32 (rx ry : BitVec 64) : (rorw rx (-ry)).setWidth 32 = goRotl 32 rx ry := by
  unfold_rot; bv_decide
/-- ARM64.rules:74 `(RotateLeft64 x y) => (ROR x (NEG y))` -/
theorem arm64_rotl64 (rx ry : BitVec 64) : ror rx (-ry) = goRotl 64 rx ry := by
  unfold_rot; bv_decide
/-- ARM64.rules:69 `(RotateLeft8 <t> x (MOVDconst [c])) => (Or8 (Lsh8x64 x (MOVDconst [c&7])) (Rsh8Ux64 x (MOVDconst [-c&7])))`
(right-hand side in generic Go semantics: shifts by a 64-bit amount, saturating). -/
theorem arm64_rotl8_const (rx c : BitVec 64) :
    (rx.setWidth 8 <<< (c &&& 7)) ||| (rx.setWidth 8 >>> ((-c) &&& 7)) = goRotl 8 rx c := by
  unfold_rot; bv_decide
/-- ARM64.rules:71 (16-bit analogue of :69) -/
theorem arm64_rotl16_const (rx c : BitVec 64) :
    (rx.setWidth 16 <<< (c &&& 15)) ||| (rx.setWidth 16 >>> ((-c) &&& 15)) = goRotl 16 rx c := by
  unfold_rot; bv_decide
/-- ARM64.rules:1025-1026 `(ROR x (MOVDconst [c])) => (RORconst x [c&63])`, `(RORW x (MOVDconst [c])) => (RORWconst x [c&31])` -/
theorem arm64_ror_const (rx c : BitVec 64) : ror rx c = rotr rx (c &&& 63) ∧
    rorw rx c = (rotr (rx.setWidth 32) ((c &&& 31).setWidth 32)).setWidth 64 := by
  unfold_rot; constructor <;> bv_decide

-- ---------------------------------------------------------------- AMD64

/-- AMD64.rules:566-569 `(RotateLeftN ...) => (ROL{B,W,L,Q} ...)` -/
theorem amd64_rotl (rx ry : BitVec 64) :
    (rolb rx ry).setWidth 8 = goRotl 8 rx ry ∧ (rolw rx ry).setWidth 16 = goRotl 16 rx ry ∧
    (roll rx ry).setWidth 32 = goRotl 32 rx ry ∧ rolq rx ry = goRotl 64 rx ry := by
  unfold_rot; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide
/-- AMD64.rules:824-833 `(ROLx x (NEG(Q|L) y)) => (RORx x y)` and `(RORx x (NEG(Q|L) y)) => (ROLx x y)` -/
theorem amd64_rol_neg (rx ry : BitVec 64) :
    rolq rx (negq ry) = rorq rx ry ∧ rolq rx (negl ry) = rorq rx ry ∧
    roll rx (negq ry) = rorl rx ry ∧ roll rx (negl ry) = rorl rx ry ∧
    rolw rx (negq ry) = rorw' rx ry ∧ rolw rx (negl ry) = rorw' rx ry ∧
    rolb rx (negq ry) = rorb rx ry ∧ rolb rx (negl ry) = rorb rx ry := by
  unfold_rot; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide
theorem amd64_ror_neg (rx ry : BitVec 64) :
    rorq rx (negq ry) = rolq rx ry ∧ rorq rx (negl ry) = rolq rx ry ∧
    rorl rx (negq ry) = roll rx ry ∧ rorl rx (negl ry) = roll rx ry ∧
    rorw' rx (negq ry) = rolw rx ry ∧ rorw' rx (negl ry) = rolw rx ry ∧
    rorb rx (negq ry) = rolb rx ry ∧ rorb rx (negl ry) = rolb rx ry := by
  unfold_rot; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide
/-- AMD64.rules:836-844 `(ROLx x (MOV(Q|L)const [c])) => (ROLxconst [int8(c&m)] x)`,
`(RORx x (MOV(Q|L)const [c])) => (ROLxconst [int8((-c)&m)] x)` with m = 63/31/15/7 -/
theorem amd64_rot_const (rx c : BitVec 64) :
    rolq rx c = rolq rx (c &&& 63) ∧ roll rx c = roll rx (c &&& 31) ∧
    rolw rx c = rolw rx (c &&& 15) ∧ rolb rx c = rolb rx (c &&& 7) ∧
    rorq rx c = rolq rx ((-c) &&& 63) ∧ rorl rx c = roll rx ((-c) &&& 31) ∧
    rorw' rx c = rolw rx ((-c) &&& 15) ∧ rorb rx c = rolb rx ((-c) &&& 7) := by
  unfold_rot; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

end Go.Compiler.Rotates
