import Std.Tactic.BVDecide
import GoInLean.Semantics.Int
/-!
# Go compiler SSA rewrite rules (`cmd/compile/internal/ssa/_gen/generic.rules`, go1.25.5)

Phase 6 feasibility experiment: a handful of architecture-independent
rewrite rules are modelled as equations between `BitVec` expressions and
proved (or refuted) under the rule's exact side condition. See
`docs/compiler-verification-feasibility.md` for scope and caveats.

## Modelling conventions

* An SSA value of type `intN`/`uintN` is a `BitVec N`; signedness is carried
  by the opcode (`Rsh8x64` arithmetic vs `Rsh8Ux64` logical, `Div8` vs
  `Div8u`), exactly as in the compiler.
* A shift opcode `OpXxxNx64` takes a 64-bit shift amount. For amounts
  `≥ N` the generic ops are defined to produce 0 (logical) or the sign fill
  (arithmetic) — that is Go source semantics; the *lowering* to machine
  shifts is where the compiler inserts masking/`CondSelect`, and it is out
  of scope here.
* `Const8 [c]` stores `c` as an `int64` AuxInt that must be the
  sign-extension of the 8-bit value (`cmd/compile/internal/ssa/value.go`,
  `AuxInt` "must be sign-extended"). The predicate `auxIntCanonical8` models
  this invariant; the historical bug golang/go#15175 was a violation of it.
* Side conditions (`isPowerOfTwo`, `isNonNegative`, `c < 0 && c != -1<<7`)
  are hypotheses of the theorem. `isNonNegative(n)` in the compiler is a
  static *approximation* (prove/facts); the theorem assumes the semantic
  fact `n.msb = false`, which is what the approximation must imply for the
  rule to be sound.
* Each theorem is stated at width 8 (where `decide`/`bv_decide` are
  cheapest) and at width 64 where the rule exists there; the proofs are
  identical up to the width, and the rule file is generated per width.
-/
namespace Go.Compiler.Generic
open Go

/-- `isPowerOfTwo(c)` on a signed constant: `c > 0 && c&(c-1) == 0` (`rewrite.go`).
Note that `c > 0` is a *signed* comparison on the AuxInt, so at width `w` the admissible
constants are exactly `1 << k` for `0 ≤ k ≤ w-2`; `1 << (w-1)` is the most negative value and
is handled by separate rules. -/
def isPowerOfTwo {w : Nat} (c : BitVec w) : Prop := (0#w).slt c = true ∧ c &&& (c - 1) = 0

/-- Bridging lemma at width 8 (kernel `decide` over the 256 constants): `isPowerOfTwo c` iff
`c = 1 << k` for some `k < 7`. The rule theorems below are therefore stated directly in terms of
`k` (`= log8(c)`) with the hypothesis `k < 7`, which `bv_decide` handles at any width. -/
theorem isPowerOfTwo_8_iff (c : BitVec 8) : isPowerOfTwo c ↔ ∃ k : BitVec 64, k < 7 ∧ c = 1#8 <<< k := by
  constructor
  · intro h
    have : ∃ k : Fin 7, c = 1#8 <<< k.val := by
      revert h; unfold isPowerOfTwo; revert c; decide
    obtain ⟨k, hk⟩ := this
    exact ⟨BitVec.ofNat 64 k.val, by
      have := k.isLt
      constructor
      · rw [BitVec.lt_def]; simp [BitVec.toNat_ofNat]; omega
      · rw [hk]; congr 1; simp [BitVec.toNat_ofNat]; omega⟩
  · intro h
    obtain ⟨k, hk, hc⟩ := h
    subst hc
    unfold isPowerOfTwo
    constructor <;> bv_decide (config := {timeout := 120})

-- --------------------------------------------------------------------------
-- Strength reduction: multiplication / unsigned division / unsigned modulo
-- by a power of two (generic.rules:203-206, 1013-1016, 1293-1296)

/-- RULE-MUL-POW2-8: `(Mul8 <t> n (Const8 [c])) && isPowerOfTwo(c) => (Lsh8x64 <t> n (Const64 [log8(c)]))` -/
theorem mul_pow2_8 (n : BitVec 8) (k : BitVec 64) (hk : k < 7) : n * (1#8 <<< k) = n <<< k := by
  bv_decide (config := {timeout := 120})
/-- RULE-MUL-POW2-64: general 64-bit multiplication is beyond the SAT budget, so this is proved
algebraically from core lemmas (`x <<< i = x * 2^i`), for every shift amount. -/
theorem mul_pow2_64 (n : BitVec 64) (k : BitVec 64) : n * (1#64 <<< k) = n <<< k := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
      BitVec.one_mul]

/-- RULE-DIVU-POW2-8: `(Div8u n (Const8 [c])) && isPowerOfTwo(c) => (Rsh8Ux64 n (Const64 [log8(c)]))` -/
theorem divu_pow2_8 (n : BitVec 8) (k : BitVec 64) (hk : k < 7) : n / (1#8 <<< k) = n >>> k := by
  bv_decide (config := {timeout := 120})
/-- RULE-DIVU-POW2-32 (also the `-1<<31`-style special case with k = 31) -/
theorem divu_pow2_32 (n : BitVec 32) (k : BitVec 64) (hk : k < 32) : n / (1#32 <<< k) = n >>> k := by
  bv_decide (config := {timeout := 120})
/-- RULE-DIVU-POW2-64: a 64-bit divider with a symbolic power-of-two divisor exceeds the SAT
budget; spot checks for fixed shift amounts (the rule file is instantiated per constant anyway). -/
theorem divu_pow2_64_k1 (n : BitVec 64) : n / (1#64 <<< 1) = n >>> 1 := by bv_decide (config := {timeout := 120})
theorem divu_pow2_64_k5 (n : BitVec 64) : n / (1#64 <<< 5) = n >>> 5 := by bv_decide (config := {timeout := 120})
theorem divu_pow2_64_k63 (n : BitVec 64) : n / (1#64 <<< 63) = n >>> 63 := by bv_decide (config := {timeout := 120})

/-- RULE-MODU-POW2-8: `(Mod8u <t> n (Const8 [c])) && isPowerOfTwo(c) => (And8 n (Const8 <t> [c-1]))` -/
theorem modu_pow2_8 (n : BitVec 8) (k : BitVec 64) (hk : k < 7) : n % (1#8 <<< k) = n &&& ((1#8 <<< k) - 1) := by
  bv_decide (config := {timeout := 120})
/-- RULE-MODU-POW2-32 -/
theorem modu_pow2_32 (n : BitVec 32) (k : BitVec 64) (hk : k < 32) : n % (1#32 <<< k) = n &&& ((1#32 <<< k) - 1) := by
  bv_decide (config := {timeout := 120})
/-- RULE-MODU-POW2-64 (line 1297 is the k = 63 case), spot checks. -/
theorem modu_pow2_64_k5 (n : BitVec 64) : n % (1#64 <<< 5) = n &&& ((1#64 <<< 5) - 1) := by bv_decide (config := {timeout := 120})
theorem modu_pow2_64_k63 (n : BitVec 64) : n % (1#64 <<< 63) = n &&& ((1#64 <<< 63) - 1) := by bv_decide (config := {timeout := 120})

/-- RULE-MOD-NONNEG-POW2-8: `(Mod8 <t> n (Const8 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (And8 n (Const8 <t> [c-1]))`.
`isNonNegative(n)` is a static approximation in the compiler; the theorem assumes the semantic fact. -/
theorem mod_nonneg_pow2_8 (n : BitVec 8) (k : BitVec 64) (hn : n.msb = false) (hk : k < 7) :
    n.srem (1#8 <<< k) = n &&& ((1#8 <<< k) - 1) := by
  bv_decide (config := {timeout := 120})
/-- RULE-DIV-NONNEG-POW2-8: `(Div8 n (Const8 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (Rsh8Ux64 n (Const64 [log8(c)]))` -/
theorem div_nonneg_pow2_8 (n : BitVec 8) (k : BitVec 64) (hn : n.msb = false) (hk : k < 7) :
    n.sdiv (1#8 <<< k) = n >>> k := by
  bv_decide (config := {timeout := 120})

-- --------------------------------------------------------------------------
-- Signed division by a power of two (generic.rules:1195-1214)
--   n / c = (n + ((n >> (w-1)) >>u (w - log c))) >> log c

/-- RULE-DIV-POW2-8: the four-instruction sequence for signed division by `2^k`, `k < 7`.
(A first draft allowed `k = 7`, i.e. the constant `-128`; `decide` refuted it: `isPowerOfTwo`
excludes that constant, see `isPowerOfTwo_8_iff`. Specification error, not a compiler bug.) -/
theorem div_pow2_8 (n : BitVec 8) (k : BitVec 64) (hk : k < 7) :
    n.sdiv (1#8 <<< k) = ((n + ((n.sshiftRight 7) >>> (8 - k))).sshiftRight k.toNat) := by
  bv_decide (config := {timeout := 120})
/-- RULE-DIV-POW2-32: the same at 32 bits (generic.rules:1207-1210) for all admissible `k < 31`. -/
theorem div_pow2_32 (n : BitVec 32) (k : BitVec 64) (hk : k < 31) :
    n.sdiv (1#32 <<< k) = ((n + ((n.sshiftRight 31) >>> (32 - k))).sshiftRight k.toNat) := by
  bv_decide (config := {timeout := 120})
/-- RULE-DIV-POW2-64 (generic.rules:1211-1214): symbolic `k` exceeds the SAT budget at 64 bits;
spot checks at k ∈ {1, 5, 32, 62}. -/
theorem div_pow2_64_k1 (n : BitVec 64) : n.sdiv (1#64 <<< 1) = ((n + ((n.sshiftRight 63) >>> (64 - 1))).sshiftRight 1) := by bv_decide (config := {timeout := 120})
theorem div_pow2_64_k5 (n : BitVec 64) : n.sdiv (1#64 <<< 5) = ((n + ((n.sshiftRight 63) >>> (64 - 5))).sshiftRight 5) := by bv_decide (config := {timeout := 120})
theorem div_pow2_64_k32 (n : BitVec 64) : n.sdiv (1#64 <<< 32) = ((n + ((n.sshiftRight 63) >>> (64 - 32))).sshiftRight 32) := by bv_decide (config := {timeout := 120})
theorem div_pow2_64_k62 (n : BitVec 64) : n.sdiv (1#64 <<< 62) = ((n + ((n.sshiftRight 63) >>> (64 - 62))).sshiftRight 62) := by bv_decide (config := {timeout := 120})
/-- NEGATIVE CONTROL: with `k = 63` the sequence is wrong (`n = MinInt64`), which is why the
rule's side condition excludes the most negative constant (kernel-checked refutation). -/
theorem div_pow2_64_k63_refuted :
    ¬ ∀ n : BitVec 64, n.sdiv (1#64 <<< 63) = ((n + ((n.sshiftRight 63) >>> (64 - 63))).sshiftRight 63) := by
  intro h; have := h (1#64 <<< 63); revert this; decide

-- --------------------------------------------------------------------------
-- Division by the most negative number (generic.rules:1187-1193)
--   (Div8 <t> x (Const8 [-1<<7])) => (Rsh8Ux64 (And8 <t> x (Neg8 <t> x)) (Const64 [7]))

/-- RULE-DIV-MINNEG-8 -/
theorem div_minneg_8 (x : BitVec 8) : x.sdiv (BitVec.ofInt 8 (-128)) = (x &&& -x) >>> 7 := by
  revert x; decide
/-- RULE-DIV-MINNEG-64 -/
theorem div_minneg_64 (x : BitVec 64) : x.sdiv (0x8000000000000000#64) = (x &&& -x) >>> 63 := by
  bv_decide (config := {timeout := 120})

-- --------------------------------------------------------------------------
-- Signed division by a negative constant (generic.rules:1182-1185)
--   (Div8 <t> n (Const8 [c])) && c < 0 && c != -1<<7 => (Neg8 (Div8 <t> n (Const8 <t> [-c])))

/-- RULE-DIV-NEGCONST-8 -/
theorem div_negconst_8 (n c : BitVec 8) (hc : c.msb = true) (hmin : c ≠ BitVec.ofInt 8 (-128)) :
    n.sdiv c = -(n.sdiv (-c)) := by
  bv_decide (config := {timeout := 120})

-- --------------------------------------------------------------------------
-- Shift algebra (generic.rules:455-482)

/-- RULE-LSH-LSH-8: `(Lsh8x64 (Lsh8x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Lsh8x64 x (Const64 [c+d]))` -/
theorem lsh_lsh_8 (x : BitVec 8) (c d : BitVec 64) (h : ¬ (c + d < c)) :
    (x <<< c) <<< d = x <<< (c + d) := by
  bv_decide (config := {timeout := 120})
/-- RULE-RSHU-RSHU-64 -/
theorem rshu_rshu_64 (x : BitVec 64) (c d : BitVec 64) (h : ¬ (c + d < c)) :
    (x >>> c) >>> d = x >>> (c + d) := by
  bv_decide (config := {timeout := 120})
/-- RULE-RSHU-RSH-7: `(Rsh8Ux64 (Rsh8x64 x _) (Const64 <t> [7])) => (Rsh8Ux64 x (Const64 <t> [7]))` -/
theorem rshu_rsh_7 (x : BitVec 8) (s : BitVec 64) : (x.sshiftRight s.toNat) >>> 7 = x >>> 7 := by
  bv_decide (config := {timeout := 120})
/-- RULE-LSH-RSHU-AND-8: `(Lsh8x64 i:(Rsh8Ux64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 8 => (And8 x (Const8 [int8(-1) << c]))` -/
theorem lsh_rshu_and_8 (x : BitVec 8) (c : BitVec 64) (hc : c < 8) :
    (x >>> c) <<< c = x &&& ((BitVec.ofInt 8 (-1)) <<< c) := by
  bv_decide (config := {timeout := 120})
/-- RULE-RSHU-LSH-AND-8: `(Rsh8Ux64 i:(Lsh8x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 8 => (And8 x (Const8 [int8(^uint8(0)>>c)]))` -/
theorem rshu_lsh_and_8 (x : BitVec 8) (c : BitVec 64) (hc : c < 8) :
    (x <<< c) >>> c = x &&& ((~~~(0#8)) >>> c) := by
  bv_decide (config := {timeout := 120})
/-- RULE-SHIFT-GE-WIDTH-64: `((Lsh64|Rsh64U)x64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])` -/
theorem shift_ge_width_64 (x c : BitVec 64) (hc : 64 ≤ c) : x <<< c = 0 ∧ x >>> c = 0 := by
  constructor <;> bv_decide (config := {timeout := 120})

-- --------------------------------------------------------------------------
-- Bounds-check elimination (generic.rules:257-266)
--   (IsInBounds (Rsh8Ux64 _ (Const64 [c])) (Const64 [d])) && 0 < c && c < 8 && 1<<uint(8-c)-1 < d => (ConstBool [true])

/-- RULE-BCE-RSHU-8: the index `x >> c` is `< d` whenever `2^(8-c) - 1 < d`.
`IsInBounds` compares as unsigned 64-bit values after zero extension. -/
theorem bce_rshu_8 (x : BitVec 8) (c d : BitVec 64) (hc0 : 0 < c) (hc : c < 8)
    (hd : (1#64 <<< (8 - c)) - 1 < d) :
    (x >>> c).zeroExtend 64 < d := by
  -- the shifted value is below 2^(8-c), which is ≤ d by hypothesis
  have h1 : (x >>> c).zeroExtend 64 ≤ (1#64 <<< (8 - c)) - 1 := by bv_decide (config := {timeout := 120})
  have h1' := BitVec.le_def.mp h1
  have hd' := BitVec.lt_def.mp hd
  exact BitVec.lt_def.mpr (by omega)
/-- RULE-BCE-MODU-64: `(IsInBounds (Mod64u _ y) y) => (ConstBool [true])` — needs `y ≠ 0` only
because `Mod64u x 0` would have panicked earlier; with Lean's `x % 0 = x` the unconditional
statement is false, so the hypothesis encodes the "division by zero already trapped" fact. -/
theorem bce_modu_64 (x y : BitVec 64) (hy : y ≠ 0) : x % y < y := by
  rw [BitVec.lt_def, BitVec.toNat_umod]
  apply Nat.mod_lt
  have : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

-- --------------------------------------------------------------------------
-- Constant folding of unsigned shifts and the AuxInt canonical-form invariant
-- (generic.rules:222-233; golang/go#15175)

/-- A `Const8` AuxInt is canonical when it is the sign extension of its low byte. -/
abbrev auxIntCanonical8 (a : BitVec 64) : Prop := a = (a.setWidth 8).signExtend 64

/-- RULE-FOLD-RSHU-8 (current rule): `(Rsh8Ux64 (Const8 [c]) (Const64 [d])) => (Const8 [int8(uint8(c) >> uint64(d))])`
produces a canonical AuxInt and the right value. -/
theorem fold_rshu_8_sound (c d : BitVec 64) (_hc : auxIntCanonical8 c) :
    let r : BitVec 64 := ((c.setWidth 8) >>> d).signExtend 64   -- int8(uint8(c) >> uint64(d)) as AuxInt
    auxIntCanonical8 r ∧ r.setWidth 8 = (c.setWidth 8) >>> d := by
  unfold auxIntCanonical8 at *; intro r; constructor <;> bv_decide (config := {timeout := 120})

/-- KNOWN-ISSUE-15175: the Go 1.6-era rule `(Rsh8Ux64 (Const8 [c]) (Const64 [d])) => (Const8 [uint8(c) >> uint64(d)])`
(without re-sign-extension) violates the AuxInt invariant whenever bit 7 of the result is set;
the issue's reproducer is `uint8(253) >> 0`, i.e. `c = -3`, `d = 0`. Refuted as a theorem of the
negation (kernel-checked). -/
theorem fold_rshu_8_go16_refuted :
    ¬ ∀ c d : BitVec 64, auxIntCanonical8 c →
      auxIntCanonical8 (((c.setWidth 8) >>> d).zeroExtend 64) := by
  intro h
  have := h (BitVec.ofInt 64 (-3)) 0 (by decide)
  revert this; unfold auxIntCanonical8; decide

end Go.Compiler.Generic
