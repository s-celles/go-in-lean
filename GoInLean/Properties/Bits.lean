import Std.Tactic.BVDecide
import GoInLean.Stdlib.Bits
/-!
# Properties of `math/bits`

Each theorem is registered in `targets/properties.yaml` under the id given
in its docstring. Specifications come from the Go doc comments of go1.25.5;
the oracle definitions live in `GoInLean.Semantics.BitSpec`.

Proof strategy: table lookups are first rewritten to their bit-blastable
function form (`*_eq_fn`, kernel-checked by `decide`), then `bv_decide`
closes the fixed-width goal. `bv_decide` proofs rely on a per-theorem
native-evaluation axiom (verified LRAT checker run through the compiler); see
`docs/architecture.md` for the trusted-computing-base discussion.
-/
set_option maxRecDepth 16384
namespace Go.Bits.Properties
open Go Go.Bits Go.BitSpec

/-- Rewrite set: unfold the `List.range` folds of the specs into concrete bit tests. -/
macro "unroll_spec" : tactic =>
  `(tactic| simp only [BitSpec.len, BitSpec.clz, BitSpec.ctz, BitSpec.popcount, BitSpec.reverse,
      List.range, List.range.loop, List.foldl, List.foldr, Nat.sub_zero, Nat.sub_self])

-- ---------------------------------------------------------------- Len

/-- BITS-LEN-8: `Len8 x` is the minimum number of bits required to represent x; 0 for x == 0. -/
theorem Len8_spec (x : uint8) : Len8 x = len x := by
  unfold Len8; rw [len8tab_eq_fn]; unroll_spec; unfold len8tabFn; bv_decide

/-- Index-range lemma: the final table index of `Len16/32/64` fits in 8 bits, so `tab`
on the wide index equals the table function on the truncated index. -/
theorem tab_len8_of_lt {w : Nat} (x : BitVec w) (hx : x.toNat < 256) :
    tab len8tab x = len8tabFn (x.setWidth 8) := by
  rw [← len8tab_eq_fn]; unfold tab
  have : (x.setWidth 8).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]
  rw [this]

/-- BITS-LEN-16 -/
theorem Len16_spec (x : uint16) : Len16 x = len x := by
  dsimp only [Len16]
  rw [tab_len8_of_lt _ (by split <;> bv_omega)]
  unroll_spec; unfold len8tabFn; bv_decide

/-- BITS-LEN-32 -/
theorem Len32_spec (x : uint32) : Len32 x = len x := by
  dsimp only [Len32]
  rw [tab_len8_of_lt _ (by split <;> split <;> bv_omega)]
  unroll_spec; unfold len8tabFn; bv_decide

/-- BITS-LEN-64 -/
theorem Len64_spec (x : uint64) : Len64 x = len x := by
  dsimp only [Len64]
  rw [tab_len8_of_lt _ (by split <;> split <;> split <;> bv_omega)]
  unroll_spec; unfold len8tabFn; bv_decide

/-- BITS-LZ-64: `LeadingZeros64 x` is the number of leading zero bits; 64 for x == 0. -/
theorem LeadingZeros64_spec (x : uint64) : LeadingZeros64 x = clz x := by
  unfold LeadingZeros64 clz; rw [Len64_spec]; rfl
theorem LeadingZeros32_spec (x : uint32) : LeadingZeros32 x = clz x := by
  unfold LeadingZeros32 clz; rw [Len32_spec]; rfl
theorem LeadingZeros16_spec (x : uint16) : LeadingZeros16 x = clz x := by
  unfold LeadingZeros16 clz; rw [Len16_spec]; rfl
theorem LeadingZeros8_spec (x : uint8) : LeadingZeros8 x = clz x := by
  unfold LeadingZeros8 clz; rw [Len8_spec]; rfl

-- ---------------------------------------------------------------- TrailingZeros

/-- BITS-TZ-8 -/
theorem TrailingZeros8_spec (x : uint8) : TrailingZeros8 x = ctz x := by
  unfold TrailingZeros8; rw [ntz8tab_eq_fn]; unroll_spec; unfold ntz8tabFn; bv_decide

theorem tab_deBruijn32_of_lt {w : Nat} (x : BitVec w) (hx : x.toNat < 32) :
    tab deBruijn32tab x = deBruijn32tabFn (x.setWidth 5) := by
  rw [← deBruijn32tab_eq_fn]; unfold tab
  have : (x.setWidth 5).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]
  rw [this]
theorem tab_deBruijn64_of_lt {w : Nat} (x : BitVec w) (hx : x.toNat < 64) :
    tab deBruijn64tab x = deBruijn64tabFn (x.setWidth 6) := by
  rw [← deBruijn64tab_eq_fn]; unfold tab
  have : (x.setWidth 6).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]
  rw [this]

/-- BITS-TZ-16: de Bruijn multiplication trick at 16 bits (via a 32-bit product). -/
theorem TrailingZeros16_spec (x : uint16) : TrailingZeros16 x = ctz x := by
  dsimp only [TrailingZeros16]
  rw [tab_deBruijn32_of_lt _ (by bv_omega)]
  unroll_spec; unfold deBruijn32tabFn deBruijn32 Go.convU; bv_decide

/-- BITS-TZ-32 -/
theorem TrailingZeros32_spec (x : uint32) : TrailingZeros32 x = ctz x := by
  dsimp only [TrailingZeros32]
  rw [tab_deBruijn32_of_lt _ (by bv_omega)]
  unroll_spec; unfold deBruijn32tabFn deBruijn32; bv_decide

/-- BITS-TZ-64 -/
theorem TrailingZeros64_spec (x : uint64) : TrailingZeros64 x = ctz x := by
  dsimp only [TrailingZeros64]
  rw [tab_deBruijn64_of_lt _ (by bv_omega)]
  unroll_spec; unfold deBruijn64tabFn deBruijn64; bv_decide

-- ---------------------------------------------------------------- OnesCount

/-- BITS-POP-8 -/
theorem OnesCount8_spec (x : uint8) : OnesCount8 x = popcount x := by
  unfold OnesCount8; rw [pop8tab_eq_fn]; unroll_spec; unfold pop8tabFn; bv_decide

/-- Generic index-range lemma: if the (wide) index is `< 256`, indexing the
table equals the bit-blastable table function applied to the low byte. -/
theorem tab_lt {w : Nat} (t : Array (BitVec 8)) (f : BitVec 8 → BitVec 8)
    (hf : ∀ i : BitVec 8, tab t i = f i)
    (x : BitVec w) (hx : x < BitVec.ofNat w 256) (hw : 256 < 2 ^ w) :
    tab t x = f (x.setWidth 8) := by
  rw [← hf]; unfold tab
  have hx' : x.toNat < 256 := by
    have := BitVec.lt_def.mp hx
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at this
  have : (x.setWidth 8).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx']
  rw [this]

/-- BITS-POP-16 -/
theorem OnesCount16_spec (x : uint16) : OnesCount16 x = popcount x := by
  dsimp only [OnesCount16]
  rw [tab_lt _ _ pop8tab_eq_fn (x >>> 8) (by bv_decide) (by decide),
      tab_lt _ _ pop8tab_eq_fn (x &&& 0xff) (by bv_decide) (by decide)]
  unroll_spec; unfold pop8tabFn; bv_decide

/-- BITS-POP-32 -/
theorem OnesCount32_spec (x : uint32) : OnesCount32 x = popcount x := by
  dsimp only [OnesCount32]
  rw [tab_lt _ _ pop8tab_eq_fn (x >>> 24) (by bv_decide) (by decide),
      tab_lt _ _ pop8tab_eq_fn ((x >>> 16) &&& 0xff) (by bv_decide) (by decide),
      tab_lt _ _ pop8tab_eq_fn ((x >>> 8) &&& 0xff) (by bv_decide) (by decide),
      tab_lt _ _ pop8tab_eq_fn (x &&& 0xff) (by bv_decide) (by decide)]
  unroll_spec; unfold pop8tabFn; bv_decide

/-- BITS-POP-64: the SWAR ("Hacker's Delight") algorithm. -/
theorem OnesCount64_spec (x : uint64) : OnesCount64 x = popcount x := by
  dsimp only [OnesCount64, m0, m1, m2]; unroll_spec; bv_decide

-- ---------------------------------------------------------------- RotateLeft

/-- BITS-ROTL-64: `RotateLeft64 x k` is x rotated left by `k mod 64` bits (Go `int` k;
negative k rotates right). The oracle is core `BitVec.rotateLeft`. -/
theorem RotateLeft64_spec (x : uint64) (k : int) :
    RotateLeft64 x k = x.rotateLeft (k.toNat % 64) := by
  dsimp only [RotateLeft64]
  have hs : (k &&& (64 - 1)).toNat = k.toNat % 64 := by
    have h1 : k &&& (64 - 1) = k % 64 := by bv_decide
    rw [h1, BitVec.toNat_umod]; rfl
  have hlt : k.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hlt, BitVec.rotateLeftAux,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hs, BitVec.toNat_sub, hs]
  have h64 : (2 : Nat) ^ UintSize = 18446744073709551616 := by decide
  have h64' : (64 : uint).toNat = 64 := rfl
  simp only [h64, h64']
  congr 2
  omega

/-- Same statement for the three narrower widths. -/
theorem RotateLeft32_spec (x : uint32) (k : int) :
    RotateLeft32 x k = x.rotateLeft (k.toNat % 32) := by
  dsimp only [RotateLeft32]
  have hs : (k &&& (32 - 1)).toNat = k.toNat % 32 := by
    have h1 : k &&& (32 - 1) = k % 32 := by bv_decide
    rw [h1, BitVec.toNat_umod]; rfl
  have hlt : k.toNat % 32 < 32 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hlt, BitVec.rotateLeftAux,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hs, BitVec.toNat_sub, hs]
  have h64 : (2 : Nat) ^ UintSize = 18446744073709551616 := by decide
  have h32' : (32 : uint).toNat = 32 := rfl
  simp only [h64, h32']
  congr 2
  omega
theorem RotateLeft16_spec (x : uint16) (k : int) :
    RotateLeft16 x k = x.rotateLeft (k.toNat % 16) := by
  dsimp only [RotateLeft16]
  have hs : (k &&& (16 - 1)).toNat = k.toNat % 16 := by
    have h1 : k &&& (16 - 1) = k % 16 := by bv_decide
    rw [h1, BitVec.toNat_umod]; rfl
  have hlt : k.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hlt, BitVec.rotateLeftAux,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hs, BitVec.toNat_sub, hs]
  have h64 : (2 : Nat) ^ UintSize = 18446744073709551616 := by decide
  have h16' : (16 : uint).toNat = 16 := rfl
  simp only [h64, h16']
  congr 2
  omega
theorem RotateLeft8_spec (x : uint8) (k : int) :
    RotateLeft8 x k = x.rotateLeft (k.toNat % 8) := by
  dsimp only [RotateLeft8]
  have hs : (k &&& (8 - 1)).toNat = k.toNat % 8 := by
    have h1 : k &&& (8 - 1) = k % 8 := by bv_decide
    rw [h1, BitVec.toNat_umod]; rfl
  have hlt : k.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hlt, BitVec.rotateLeftAux,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hs, BitVec.toNat_sub, hs]
  have h64 : (2 : Nat) ^ UintSize = 18446744073709551616 := by decide
  have h8' : (8 : uint).toNat = 8 := rfl
  simp only [h64, h8']
  congr 2
  omega

/-- BITS-ROTL-NEG-64: doc: "To rotate x right by k bits, call RotateLeft(x, -k)". -/
theorem RotateLeft64_neg (x : uint64) (k : int) :
    RotateLeft64 x (-k) = x.rotateRight (k.toNat % 64) := by
  rw [RotateLeft64_spec]
  -- rotateRight by r equals rotateLeft by (64 - r) % 64; both sides are now
  -- concrete BitVec functions of a `Nat` amount < 64: case-split on the 64 values.
  have hk : (-k).toNat % 64 = (64 - k.toNat % 64) % 64 := by
    have h1 : -k = (0 : uint) - k := by rfl
    rw [h1, BitVec.toNat_sub]
    have h64 : (2 : Nat) ^ UintSize = 18446744073709551616 := by decide
    have h0 : (0 : uint).toNat = 0 := rfl
    simp only [h64, h0]; omega
  rw [hk]
  generalize hr : k.toNat % 64 = r
  have hr64 : r < 64 := by omega
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr64]
  -- after fixing r, rotateLeft ((64 - r) % 64) is rotateLeftAux unless r = 0
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0; simp only [BitVec.rotateRightAux, BitVec.rotateLeft, BitVec.rotateLeftAux]; bv_decide
  · rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt (by omega)]
    simp only [BitVec.rotateLeftAux, BitVec.rotateRightAux]
    have : (64 - r) % 64 = 64 - r := Nat.mod_eq_of_lt (by omega)
    rw [this]
    have : 64 - (64 - r) = r := by omega
    rw [this, BitVec.or_comm]

-- ---------------------------------------------------------------- ReverseBytes / Reverse

/-- BITS-REVB-16 -/
theorem ReverseBytes16_spec (x : uint16) : ReverseBytes16 x = reverseBytes16 x := by
  dsimp only [ReverseBytes16, reverseBytes16]; bv_decide
/-- BITS-REVB-32 -/
theorem ReverseBytes32_spec (x : uint32) : ReverseBytes32 x = reverseBytes32 x := by
  dsimp only [ReverseBytes32, reverseBytes32, m3, Go.convU]; bv_decide
/-- BITS-REVB-64 -/
theorem ReverseBytes64_spec (x : uint64) : ReverseBytes64 x = reverseBytes64 x := by
  dsimp only [ReverseBytes64, reverseBytes64, m3, m4]; bv_decide

/-- BITS-REV-8 -/
theorem Reverse8_spec (x : uint8) : Reverse8 x = reverse x := by
  unfold Reverse8; rw [rev8tab_eq_fn]; unroll_spec; unfold rev8tabFn; bv_decide
/-- BITS-REV-16 -/
theorem Reverse16_spec (x : uint16) : Reverse16 x = reverse x := by
  dsimp only [Reverse16]
  rw [tab_lt _ _ rev8tab_eq_fn (x >>> 8) (by bv_decide) (by decide),
      tab_lt _ _ rev8tab_eq_fn (x &&& 0xff) (by bv_decide) (by decide)]
  unroll_spec; unfold rev8tabFn; bv_decide
/-- BITS-REV-32 -/
theorem Reverse32_spec (x : uint32) : Reverse32 x = reverse x := by
  dsimp only [Reverse32, ReverseBytes32, m0, m1, m2, m3, Go.convU]; unroll_spec; bv_decide
/-- BITS-REV-64 -/
theorem Reverse64_spec (x : uint64) : Reverse64 x = reverse x := by
  dsimp only [Reverse64, ReverseBytes64, m0, m1, m2, m3, m4]; unroll_spec; bv_decide

-- ---------------------------------------------------------------- Add / Sub

/-- BITS-ADD-64: doc: "sum = x + y + carry. The carry input must be 0 or 1 …
The carryOut output is guaranteed to be 0 or 1." Stated as a 128-bit identity. -/
theorem Add64_spec (x y carry : uint64) (hc : carry = 0 ∨ carry = 1) :
    ((Add64 x y carry).2.zeroExtend 128 <<< 64) ||| (Add64 x y carry).1.zeroExtend 128
      = x.zeroExtend 128 + y.zeroExtend 128 + carry.zeroExtend 128 := by
  dsimp only [Add64, Go.andNot]; bv_decide
theorem Add64_carryOut_le_one (x y carry : uint64) : (Add64 x y carry).2 ≤ 1 := by
  dsimp only [Add64, Go.andNot]; bv_decide
/-- BITS-ADD-32 -/
theorem Add32_spec (x y carry : uint32) (hc : carry = 0 ∨ carry = 1) :
    ((Add32 x y carry).2.zeroExtend 64 <<< 32) ||| (Add32 x y carry).1.zeroExtend 64
      = x.zeroExtend 64 + y.zeroExtend 64 + carry.zeroExtend 64 := by
  dsimp only [Add32, Go.convU]; bv_decide

/-- BITS-SUB-64: doc: "diff = x - y - borrow. The borrow input must be 0 or 1 …
The borrowOut output is guaranteed to be 0 or 1." As a 128-bit identity:
x = y + borrow + diff - borrowOut·2^64. -/
theorem Sub64_spec (x y borrow : uint64) (hb : borrow = 0 ∨ borrow = 1) :
    x.zeroExtend 128 = y.zeroExtend 128 + borrow.zeroExtend 128 + (Sub64 x y borrow).1.zeroExtend 128
      - ((Sub64 x y borrow).2.zeroExtend 128 <<< 64) := by
  dsimp only [Sub64]; bv_decide
theorem Sub64_borrowOut_le_one (x y borrow : uint64) : (Sub64 x y borrow).2 ≤ 1 := by
  dsimp only [Sub64]; bv_decide
/-- BITS-SUB-32 -/
theorem Sub32_spec (x y borrow : uint32) (hb : borrow = 0 ∨ borrow = 1) :
    x.zeroExtend 64 = y.zeroExtend 64 + borrow.zeroExtend 64 + (Sub32 x y borrow).1.zeroExtend 64
      - ((Sub32 x y borrow).2.zeroExtend 64 <<< 32) := by
  dsimp only [Sub32]; bv_decide

-- ---------------------------------------------------------------- Mul

/-- BITS-MUL-32: `(hi, lo)` is the 64-bit product. -/
theorem Mul32_spec (x y : uint32) :
    (Mul32 x y).1 ++ (Mul32 x y).2 = x.zeroExtend 64 * y.zeroExtend 64 := by
  dsimp only [Mul32, Go.convU]
  generalize x.zeroExtend 64 * y.zeroExtend 64 = t
  bv_decide

/-- Oracle for the high half of a product at width `2h`. -/
def mulhiSpec (h : Nat) (x y : BitVec (2*h)) : BitVec (2*h) :=
  ((x.zeroExtend (4*h) * y.zeroExtend (4*h)) >>> (2*h)).setWidth (2*h)

/-- BITS-MULHI-8: the `Mul64` high-half algorithm instantiated at width 8 (h = 4). -/
theorem mulhiGeneric_4 (x y : BitVec 8) : mulhiGeneric 4 x y = mulhiSpec 4 x y := by
  dsimp only [mulhiGeneric, mulhiSpec]; bv_decide
-- The SAT encoding of general multiplication beyond 8×8 bits exceeds the
-- solver budget (h = 8 fails at 400 s); see targets/properties.yaml (BITS-MUL-64,
-- status `inconclusive`). `Mul64` is definitionally `mulhiGeneric 32`.
theorem Mul64_lo (x y : uint64) : (Mul64 x y).2 = x * y := rfl
theorem Mul64_hi_def (x y : uint64) : (Mul64 x y).1 = mulhiGeneric 32 x y := rfl

-- A Nat-level algebraic proof of the 64-bit high half (schoolbook identity by `grind`,
-- then `omega` over product atoms) type-checks in isolation but not yet inside this file
-- (heartbeat budget / lemma names); it is kept out until it builds in CI. See the report.

-- ---------------------------------------------------------------- Div / Rem

/-- Oracle: the `2h`-bit quotient and remainder of the `4h`-bit dividend `hi·2^{2h} + lo`. -/
def divSpec (h : Nat) (hi lo y : BitVec (2*h)) : BitVec (2*h) × BitVec (2*h) :=
  let z : BitVec (4*h) := hi.zeroExtend (4*h) <<< (2*h) ||| lo.zeroExtend (4*h)
  let yz : BitVec (4*h) := y.zeroExtend (4*h)
  ((z / yz).setWidth (2*h), (z % yz).setWidth (2*h))

/-- The model's `clzW` oracle used inside `divGeneric` agrees with `clz` at 64 bits … -/
theorem clzW_eq_clz64 (x : BitVec 64) : clzW x = clz x := by
  dsimp only [BitSpec.clzW, BitSpec.clz, BitSpec.len]
  simp only [List.range, List.range.loop, List.foldl, Nat.reduceSub]
  bv_decide
/-- … and therefore with Go's `LeadingZeros64`, which `Div64` calls for the normalisation shift. -/
theorem LeadingZeros64_eq_clzW (y : uint64) : LeadingZeros64 y = clzW y := by
  rw [LeadingZeros64_spec, clzW_eq_clz64]

/-- BITS-DIV-PANIC (1/3): `y == 0` panics with `divideError`, for every half-width. -/
theorem divGeneric_divide (h : Nat) (hi lo y : BitVec (2*h)) (hy : y = 0) :
    divGeneric h hi lo y = .error .divideError := by
  simp [divGeneric, hy]
/-- BITS-DIV-PANIC (2/3): `y <= hi` (with `y != 0`) panics with `overflowError`. -/
theorem divGeneric_overflow (h : Nat) (hi lo y : BitVec (2*h)) (hy : y ≠ 0) (hle : y ≤ hi) :
    divGeneric h hi lo y = .error .overflowError := by
  have hy' : ¬ (y = 0#(2*h)) := hy
  simp [divGeneric, hy', hle]
/-- BITS-DIV-PANIC (3/3): otherwise `Div` returns normally. -/
theorem divGeneric_ok (h : Nat) (hi lo y : BitVec (2*h)) (hy : y ≠ 0) (hlt : hi < y) :
    ∃ r, divGeneric h hi lo y = .ok r := by
  have hle : ¬ y ≤ hi := BitVec.not_le.mpr hlt
  unfold divGeneric
  simp only [hy, hle, ↓reduceIte]
  split <;> exact ⟨_, rfl⟩

/-- BITS-DIV-8 (hi = 0 branch): the fast path is correct at width 8. -/
theorem divGeneric_4_hi0 (lo y : BitVec 8) (hy : y ≠ 0) :
    divGeneric 4 0 lo y = .ok (divSpec 4 0 lo y) := by
  have hle : ¬ y ≤ 0 := by bv_decide
  unfold divGeneric
  simp only [hy, hle, ↓reduceIte]
  dsimp only [divSpec]
  simp only [Except.ok.injEq, Prod.mk.injEq]
  constructor <;> bv_decide

set_option maxHeartbeats 20000000 in
/-- BITS-DIV-8 (general branch, `hi ≠ 0`): the Knuth long-division algorithm of `Div64`,
instantiated at width 8 (half-width 4) with both correction loops unrolled (fuel 8), returns
the exact quotient and remainder whenever Go does not panic. `bv_decide`'s preprocessing of the
unrolled term needs a large heartbeat budget (≈ 80 s on an M-series laptop). -/
theorem divGeneric_4_spec (hi lo y : BitVec 8) (hy : y ≠ 0) (hhi : hi < y) :
    divGeneric 4 hi lo y = .ok (divSpec 4 hi lo y) := by
  have hle : ¬ y ≤ hi := BitVec.not_le.mpr hhi
  unfold divGeneric
  simp only [hy, hle, ↓reduceIte]
  split
  · rename_i h0; subst h0
    dsimp only [divSpec]
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor <;> bv_decide
  · dsimp only [divSpec, BitSpec.clzW]
    simp only [List.range, List.range.loop, List.foldl, divCorrect, Except.ok.injEq, Prod.mk.injEq,
      Nat.reduceMul, Nat.reduceSub]
    constructor
    · bv_decide (config := {timeout := 900})
    · bv_decide (config := {timeout := 900})

-- ---------------------------------------------------------------- Negative control

/-- BITS-ADD-64-NOPRE: *without* the documented precondition `carry ∈ {0,1}` the
128-bit identity is false. This is a model-level counterexample that is **not** a
Go bug (golang/go#54255): the refutation is recorded as a kernel-checked theorem,
following julia-in-lean's convention for refuted entries. -/
theorem Add64_nopre_refuted :
    ¬ ∀ x y carry : uint64,
      ((Add64 x y carry).2.zeroExtend 128 <<< 64) ||| (Add64 x y carry).1.zeroExtend 128
        = x.zeroExtend 128 + y.zeroExtend 128 + carry.zeroExtend 128 := by
  intro h
  have := h 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 2
  revert this
  decide

end Go.Bits.Properties
