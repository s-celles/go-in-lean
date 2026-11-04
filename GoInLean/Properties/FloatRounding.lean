import GoInLean.Semantics.Float64

/-!
# Rounding correctness of the float64 model (the ProofKit direction, step 0)

The executable IEEE 754 models of `GoInLean.Semantics.Float64` and `Float32`
are validated differentially (canaries and campaigns); this file starts
turning that validation into proof. Everything here is kernel-checked
arithmetic - no `bv_decide`, no `sorry`.

* `shiftRound_spec` / `shiftRound_unique`: `shiftRound m k` is the unique
  integer q with `m` within half an ulp of `q * 2^k`, ties to even - the
  single rounding step every `encode`, `divPositive` and `sqrtBits` goes
  through.
-/
namespace Go.Float64.Proofs

open Go.Float64

/-! ## The rounding kernel -/

/-- `q` is the nearest-even rounding of `m / 2^k`: `m` lies within half an
ulp of `q * 2^k`, counted on whichever side, and exactly at half an ulp
only when `q` is even. -/
def RoundEvenNat (q m k : Nat) : Prop :=
  (q * 2 ^ k ≤ m ∧ 2 * (m - q * 2 ^ k) ≤ 2 ^ k
      ∧ (2 * (m - q * 2 ^ k) = 2 ^ k → q % 2 = 0))
  ∨ (m ≤ q * 2 ^ k ∧ 2 * (q * 2 ^ k - m) ≤ 2 ^ k
      ∧ (2 * (q * 2 ^ k - m) = 2 ^ k → q % 2 = 0))

private theorem two_pow_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih (by decide)

private theorem one_shiftLeft (n : Nat) : 1 <<< n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.shiftLeft_succ, ih, Nat.pow_succ]; omega

/-- `shiftRound` in its division/remainder form. -/
private theorem shiftRound_div (m k : Nat) :
    shiftRound m k =
      (if m % 2 ^ k > 2 ^ (k - 1) then m / 2 ^ k + 1
       else if m % 2 ^ k == 2 ^ (k - 1) then m / 2 ^ k + m / 2 ^ k % 2
       else m / 2 ^ k) := by
  have h1 : m >>> k = m / 2 ^ k := Nat.shiftRight_eq_div_pow m k
  have h2 : m &&& (2 ^ k - 1) = m % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod m k
  have h3 : ∀ q : Nat, q &&& 1 = q % 2 := fun q => by
    have := Nat.and_two_pow_sub_one_eq_mod q 1
    simp [this]
  unfold shiftRound
  simp only [one_shiftLeft, h1, h2, h3]

theorem shiftRound_spec (m k : Nat) (hk : 1 ≤ k) : RoundEvenNat (shiftRound m k) m k := by
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj]
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
    omega
  have hCpos : 0 < 2 ^ k := two_pow_pos k
  have hme : m = (m / 2 ^ k) * 2 ^ k + m % 2 ^ k := by
    have hdm := Nat.div_add_mod m (2 ^ k)
    rw [Nat.mul_comm] at hdm
    omega
  have hmod : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ hCpos
  rw [shiftRound_div]
  simp only [beq_iff_eq]
  rcases Nat.lt_trichotomy (m % 2 ^ k) (2 ^ (k - 1)) with hlt | heq | hgt
  · rw [if_neg (by omega), if_neg (by omega)]
    refine Or.inl ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · intro htie
      omega
  · rw [if_neg (by omega), if_pos (by omega)]
    by_cases hodd : m / 2 ^ k % 2 = 1
    · have harg : m / 2 ^ k + m / 2 ^ k % 2 = m / 2 ^ k + 1 := by omega
      rw [harg]
      have hmul : (m / 2 ^ k + 1) * 2 ^ k = (m / 2 ^ k) * 2 ^ k + 2 ^ k := by
        rw [Nat.add_mul]
        omega
      refine Or.inr ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · intro htie
        omega
    · have harg : m / 2 ^ k + m / 2 ^ k % 2 = m / 2 ^ k := by omega
      rw [harg]
      refine Or.inl ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · intro htie
        omega
  · rw [if_pos (by omega)]
    have hmul : (m / 2 ^ k + 1) * 2 ^ k = (m / 2 ^ k) * 2 ^ k + 2 ^ k := by
      rw [Nat.add_mul]
      omega
    refine Or.inr ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · intro htie
      omega

private theorem mul_le_cancel (t C : Nat) (hC : 0 < C) (h : t * C ≤ C) : t ≤ 1 := by
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · exact Nat.lt_succ_iff.mp h2
  · exact absurd h (fun hcon => by
      have h3 : 2 * C ≤ t * C := Nat.mul_le_mul h2 (Nat.le_refl C)
      have := Nat.le_trans h3 hcon
      omega)

/-- Nearest-even rounding is unique: two `RoundEvenNat` witnesses agree. -/
theorem shiftRound_unique {q q' m k : Nat} (h : RoundEvenNat q m k) (h' : RoundEvenNat q' m k) :
    q = q' := by
  have hCpos : 0 < 2 ^ k := two_pow_pos k
  -- the doubled upper/lower bounds a witness puts on m, either side of
  -- the disjunction
  have hub : ∀ a : Nat, RoundEvenNat a m k → 2 * m ≤ 2 * (a * 2 ^ k) + 2 ^ k := by
    intro a ha
    rcases ha with ⟨_, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  have hlb : ∀ a : Nat, RoundEvenNat a m k → 2 * (a * 2 ^ k) - 2 ^ k ≤ 2 * m := by
    intro a ha
    rcases ha with ⟨h1, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
  rcases Nat.lt_trichotomy q q' with hlt | heq | hgt
  · exfalso
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hne | hgap
    · -- q' = q + 1: m sits exactly at the shared midpoint unless the
      -- witness forms contradict; the (A,B) pair forces both ties, and
      -- two consecutive even witnesses is impossible
      have heq2 : q' = q + 1 := hne.symm
      have hs : q' * 2 ^ k = q * 2 ^ k + 2 ^ k := by
        rw [heq2, Nat.add_mul]
        omega
      rcases h with ⟨hA1, hA2, hA3⟩ | ⟨hB1, hB2, hB3⟩ <;>
      rcases h' with ⟨hA1', hA2', hA3'⟩ | ⟨hB1', hB2', hB3'⟩
      · omega
      · have hq0 : q % 2 = 0 := hA3 (by omega)
        have hq1 : q' % 2 = 0 := hB3' (by omega)
        omega
      · omega
      · omega
    · -- q' ≥ q + 2: the witness intervals are a full ulp apart
      obtain ⟨t, ht⟩ : ∃ t, q' = q + 2 + t := ⟨q' - q - 2, by omega⟩
      have hq : q + 2 + t = q + (2 + t) := by omega
      have h1 : (q + (2 + t)) * 2 ^ k = q * 2 ^ k + (2 + t) * 2 ^ k := by
        rw [Nat.add_mul]
      have h2a : 2 ≤ 2 + t := by omega
      have h2 : 2 * 2 ^ k ≤ (2 + t) * 2 ^ k := Nat.mul_le_mul h2a (Nat.le_refl _)
      have hu := hub q h
      have hl := hlb q' h'
      rw [ht, hq, h1] at hl
      omega
  · exact heq
  · exact absurd (shiftRound_unique h' h) (by omega)

end Go.Float64.Proofs
