import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
/-!
# `Mul64` at 64 bits, by an algebraic proof over `Nat`

`bv_decide` cannot bit-blast 64×64 multiplication within budget, so the
schoolbook algorithm of `bits.go:470-486` is proved by mapping every
intermediate 64-bit operation to `Nat` and showing it never wraps.
Kernel-only: no `bv_decide`, no `decide` on large terms.
-/
set_option maxRecDepth 8192
namespace Go.Bits.Properties.Mul64
open Go Go.Bits

theorem toNat_mul_nowrap (a b : BitVec 64) (h : a.toNat * b.toNat < 2^64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]
theorem toNat_add_nowrap (a b : BitVec 64) (h : a.toNat + b.toNat < 2^64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]
theorem toNat_lo32 (x : BitVec 64) : (x &&& 0xFFFFFFFF).toNat = x.toNat % 2^32 := by
  rw [BitVec.toNat_and]
  have : (0xFFFFFFFF : BitVec 64).toNat = 2^32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
theorem toNat_hi32 (x : BitVec 64) : (x >>> 32).toNat = x.toNat / 2^32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem prod_lt (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) : a * b ≤ (2^32 - 1) * (2^32 - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

/-- The schoolbook identity with base 2^32, over `Nat`. -/
theorem schoolbook (x0 x1 y0 y1 : Nat) (hx0 : x0 < 2^32) (hy0 : y0 < 2^32) :
    x1 * y1 + (x1 * y0 + (x0 * y0) / 2^32) / 2^32 + (((x1 * y0 + (x0 * y0) / 2^32) % 2^32) + x0 * y1) / 2^32
      = ((x1 * 2^32 + x0) * (y1 * 2^32 + y0)) / 2^64 := by
  have key : (x1 * 2^32 + x0) * (y1 * 2^32 + y0)
      = (x1 * y1) * 2^64 + (x1 * y0 + x0 * y1) * 2^32 + x0 * y0 := by grind
  rw [key]
  have hd := prod_lt x0 y0 hx0 hy0
  generalize x1 * y1 = a at *
  generalize x1 * y0 = b at *
  generalize x0 * y1 = c at *
  generalize x0 * y0 = d at *
  omega

/-- BITS-MUL-64 (high half). -/
theorem mulhi_toNat (x y : BitVec 64) :
    (mulhiGeneric 32 x y).toNat = (x.toNat * y.toNat) / 2^64 := by
  have hmask : ((1 : BitVec (2*32)) <<< 32) - 1 = (0xFFFFFFFF : BitVec 64) := by decide
  simp only [mulhiGeneric, hmask]
  -- name the halves and their Nat values
  generalize hX0 : x &&& 0xFFFFFFFF = X0
  generalize hX1 : x >>> 32 = X1
  generalize hY0 : y &&& 0xFFFFFFFF = Y0
  generalize hY1 : y >>> 32 = Y1
  have ex0 : X0.toNat = x.toNat % 2^32 := hX0 ▸ toNat_lo32 x
  have ey0 : Y0.toNat = y.toNat % 2^32 := hY0 ▸ toNat_lo32 y
  have ex1 : X1.toNat = x.toNat / 2^32 := hX1 ▸ toNat_hi32 x
  have ey1 : Y1.toNat = y.toNat / 2^32 := hY1 ▸ toNat_hi32 y
  have bx0 : X0.toNat < 2^32 := by rw [ex0]; exact Nat.mod_lt _ (by decide)
  have by0 : Y0.toNat < 2^32 := by rw [ey0]; exact Nat.mod_lt _ (by decide)
  have bx1 : X1.toNat < 2^32 := by rw [ex1]; have := x.isLt; omega
  have by1 : Y1.toNat < 2^32 := by rw [ey1]; have := y.isLt; omega
  have p00 := prod_lt _ _ bx0 by0
  have p10 := prod_lt _ _ bx1 by0
  have p01 := prod_lt _ _ bx0 by1
  have p11 := prod_lt _ _ bx1 by1
  -- w0 = X0*Y0
  have e_w0 : (X0 * Y0).toNat = X0.toNat * Y0.toNat := toNat_mul_nowrap _ _ (by omega)
  have e_w0s : ((X0 * Y0) >>> 32).toNat = X0.toNat * Y0.toNat / 2^32 := by
    rw [toNat_hi32, e_w0]
  -- t = X1*Y0 + w0>>32
  have e_t : (X1 * Y0 + ((X0 * Y0) >>> 32)).toNat = X1.toNat * Y0.toNat + X0.toNat * Y0.toNat / 2^32 := by
    rw [toNat_add_nowrap _ _ (by rw [toNat_mul_nowrap _ _ (by omega), e_w0s]; omega),
        toNat_mul_nowrap _ _ (by omega), e_w0s]
  generalize hT : X1 * Y0 + ((X0 * Y0) >>> 32) = T at *
  have bT : T.toNat < 2^64 := T.isLt
  -- w1 = t & mask, w2 = t >> 32, w1' = w1 + X0*Y1
  have e_w1 : (T &&& 0xFFFFFFFF).toNat = T.toNat % 2^32 := toNat_lo32 T
  have e_w2 : (T >>> 32).toNat = T.toNat / 2^32 := toNat_hi32 T
  have e_w1' : ((T &&& 0xFFFFFFFF) + X0 * Y1).toNat = T.toNat % 2^32 + X0.toNat * Y1.toNat := by
    have : T.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    rw [toNat_add_nowrap _ _ (by rw [e_w1, toNat_mul_nowrap _ _ (by omega)]; omega),
        e_w1, toNat_mul_nowrap _ _ (by omega)]
  have e_w1's : (((T &&& 0xFFFFFFFF) + X0 * Y1) >>> 32).toNat = (T.toNat % 2^32 + X0.toNat * Y1.toNat) / 2^32 := by
    rw [toNat_hi32, e_w1']
  have e_hi1 : (X1 * Y1 + (T >>> 32)).toNat = X1.toNat * Y1.toNat + T.toNat / 2^32 := by
    rw [toNat_add_nowrap _ _ (by rw [toNat_mul_nowrap _ _ (by omega), e_w2]; omega),
        toNat_mul_nowrap _ _ (by omega), e_w2]
  have hT' : T.toNat = X1.toNat * Y0.toNat + X0.toNat * Y0.toNat / 2^32 := e_t
  rw [toNat_add_nowrap _ _ (by rw [e_hi1, e_w1's]; omega), e_hi1, e_w1's, hT']
  have hsb := schoolbook X0.toNat X1.toNat Y0.toNat Y1.toNat bx0 by0
  have hx : X1.toNat * 2^32 + X0.toNat = x.toNat := by rw [ex1, ex0]; exact Nat.div_add_mod' _ _
  have hy : Y1.toNat * 2^32 + Y0.toNat = y.toNat := by rw [ey1, ey0]; exact Nat.div_add_mod' _ _
  rw [hx, hy] at hsb
  exact hsb

/-- BITS-MUL-64: `(hi, lo) = x * y` as a 128-bit product. -/
theorem Mul64_spec (x y : uint64) :
    (Mul64 x y).1 ++ (Mul64 x y).2 = x.zeroExtend 128 * y.zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2^128 := by
    calc _ < 2^64 * 2^64 := Nat.mul_lt_mul'' hx hy
      _ = 2^128 := by decide
  simp only [Mul64, BitVec.toNat_append, BitVec.toNat_mul, BitVec.toNat_setWidth, mulhi_toNat]
  have hlo : (x.toNat * y.toNat) % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2^128), Nat.mod_eq_of_lt (by omega : y.toNat < 2^128),
      Nat.mod_eq_of_lt hxy]
  omega

end Go.Bits.Properties.Mul64
