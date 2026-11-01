import Std.Tactic.BVDecide
import GoInLean.Properties.Mul64
/-!
# Length-overflow guards in `strings`, `bytes`, `slices` (go1.25.5)

* `strings.Repeat` (strings.go), `bytes.Repeat`, `slices.Repeat` (slices.go:512-528):
  `hi, lo := bits.Mul(uint(len), uint(count)); if hi > 0 || lo > maxInt { panic }`.
* `slices.Concat` (slices.go:489-506): `size += len(s); if size < 0 { panic }`.
* `strings.Join` / `bytes.Join`: `if len(sep) >= maxInt/(len(elems)-1) { panic }`,
  then `if len(elem) > maxInt-n { panic }` before each `n += len(elem)`.

Lengths are Go `int`s in `[0, maxInt]`, `maxInt = 2^63 - 1` (A1). Each guard is
transliterated on `BitVec 64` and related to the exact `Nat` arithmetic.
-/
namespace Go.Overflow
open Go Go.Bits

/-- `math.MaxInt` on 64-bit targets, as a literal so that `omega` sees a number. -/
local notation "MaxInt" => (9223372036854775807 : Nat)

/-- Repeat guard, transliterated: `hi > 0 || lo > maxInt`. -/
def repeatPanics (len count : BitVec 64) : Bool :=
  let (hi, lo) := Mul64 len count
  hi > 0 || lo > Go.maxInt

/-- REPEAT-GUARD-EXACT: the `Repeat` guard panics iff the exact product `len·count` exceeds
`maxInt` (no false alarm, no missed overflow), for all 64-bit inputs. -/
theorem repeatPanics_iff (len count : BitVec 64) :
    repeatPanics len count = true ↔ len.toNat * count.toNat > MaxInt := by
  have hspec := Go.Bits.Properties.Mul64.mulhi_toNat len count
  unfold repeatPanics
  simp only [Mul64, Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, BitVec.lt_def]
  have hlo : (len * count).toNat = (len.toNat * count.toNat) % 2^64 := BitVec.toNat_mul _ _
  have hmax : Go.maxInt.toNat = 9223372036854775807 := by decide
  rw [hspec, hlo, hmax]
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  rw [h0]
  generalize len.toNat * count.toNat = P
  omega

/-- One step of `Concat`'s loop: with `size, l ∈ [0, maxInt]`, the wrapped sum is negative
iff the exact sum exceeds `maxInt`; otherwise it is exact. -/
theorem concat_step (size l : BitVec 64) (hs : size.msb = false) (hl : l.msb = false) :
    ((size + l).msb = true ↔ size.toNat + l.toNat > MaxInt) ∧
    ((size + l).msb = false → (size + l).toNat = size.toNat + l.toNat) := by
  have hs' : size.toNat < 2^63 := by
    have := BitVec.msb_eq_false_iff_two_mul_lt.mp hs; omega
  have hl' : l.toNat < 2^63 := by
    have := BitVec.msb_eq_false_iff_two_mul_lt.mp hl; omega
  have hsum : (size + l).toNat = size.toNat + l.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  constructor
  · rw [BitVec.msb_eq_decide, hsum]; simp; omega
  · intro _; exact hsum

/-- The `Concat` size loop on a list of lengths (Go `int`s, each `≥ 0`):
`none` = panic "len out of range", `some n` = total size. -/
def concatSize : BitVec 64 → List (BitVec 64) → Option (BitVec 64)
  | size, [] => some size
  | size, l :: ls => if (size + l).msb then none else concatSize (size + l) ls

/-- CONCAT-GUARD-EXACT: `Concat` panics iff some prefix sum of the lengths exceeds `maxInt`
(equivalently, since lengths are non-negative, iff the total does), and otherwise computes
the exact total. -/
theorem concatSize_spec (ls : List (BitVec 64)) (hls : ∀ l ∈ ls, l.msb = false)
    (size : BitVec 64) (hs : size.msb = false) :
    (concatSize size ls = none ↔ size.toNat + (ls.map BitVec.toNat).sum > MaxInt) ∧
    (∀ n, concatSize size ls = some n → n.toNat = size.toNat + (ls.map BitVec.toNat).sum) := by
  induction ls generalizing size with
  | nil =>
    simp only [concatSize, List.map_nil, List.sum_nil, Nat.add_zero]
    have : size.toNat < 2^63 := by have := BitVec.msb_eq_false_iff_two_mul_lt.mp hs; omega
    constructor
    · simp; omega
    · intro n h; simp at h; subst h; rfl
  | cons l rest ih =>
    have hl := hls l (List.mem_cons_self ..)
    have hrest : ∀ l' ∈ rest, l'.msb = false := fun l' h => hls l' (List.mem_cons_of_mem _ h)
    obtain ⟨hneg, hexact⟩ := concat_step size l hs hl
    simp only [concatSize, List.map_cons, List.sum_cons]
    by_cases hm : (size + l).msb = true
    · simp only [hm, ↓reduceIte]
      have := hneg.mp hm
      constructor
      · simp; omega
      · intro n h; simp at h
    · have hm' : (size + l).msb = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨ih1, ih2⟩ := ih hrest (size + l) hm'
      have he := hexact hm'
      constructor
      · rw [ih1, he]; constructor <;> intro <;> omega
      · intro n h; rw [ih2 n h, he]; omega

/-- `Join`'s separator guard, transliterated: `len(sep) >= maxInt/(len(elems)-1)` with
`k = len(elems)-1 ≥ 1` (signed division of non-negative values = unsigned). -/
def joinSepPanics (sep k : BitVec 64) : Bool := sep ≥ Go.maxInt / k

/-- JOIN-GUARD-SOUND: whenever the separator guard does not panic, `len(sep)·k` fits in an
`int` (the guard never misses an overflow). -/
theorem joinSep_sound (sep k : BitVec 64) (hk : 0 < k.toNat) (_hsep : sep.toNat ≤ MaxInt)
    (h : joinSepPanics sep k = false) : sep.toNat * k.toNat ≤ MaxInt := by
  unfold joinSepPanics at h
  simp only [decide_eq_false_iff_not, BitVec.not_le] at h
  have h' := BitVec.lt_def.mp h
  rw [BitVec.toNat_udiv] at h'
  have hmax : Go.maxInt.toNat = 9223372036854775807 := by decide
  rw [hmax] at h'
  -- sep < (2^63-1)/k  ⇒  sep*k < 2^63-1
  have := (Nat.lt_div_iff_mul_lt hk).mp h'
  omega

/-- JOIN-GUARD-CONSERVATIVE: the guard is *not* exact — it also panics in cases where the exact
length `len(sep)·k` still fits (e.g. `k = 1`, `len(sep) = maxInt`, or `k = 3`, `len(sep) = (maxInt)/3`).
Refuted as a kernel-checked negation of exactness. -/
theorem joinSep_not_exact :
    ¬ ∀ sep k : BitVec 64, 0 < k.toNat → sep.toNat ≤ MaxInt →
      (joinSepPanics sep k = true → sep.toNat * k.toNat > MaxInt) := by
  intro h
  have := h (BitVec.ofNat 64 (MaxInt / 3)) 3 (by decide) (by decide)
  revert this; unfold joinSepPanics; decide

end Go.Overflow
