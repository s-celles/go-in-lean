import Std.Tactic.BVDecide
import GoInLean.Stdlib.Slices
/-!
# Properties of selected `slices` / `sort` functions
-/
namespace Go.Slices.Properties
open Go Go.Slices

/-- SORT-SEARCH-MID: the midpoint trick `int(uint(i+j) >> 1)` (search.go:63, "avoid overflow
when computing h") computes ⌊(i+j)/2⌋ exactly (as a 65-bit sum) for all Go `int` values
`0 ≤ i ≤ j`, and satisfies the loop invariant `i ≤ h < j` when `i < j`. -/
theorem midpoint_spec (i j : int) (hi : (0#64).sle i = true) (hij : i.sle j = true) :
    midpoint i j = ((i.zeroExtend 65 + j.zeroExtend 65) >>> 1).setWidth 64 ∧
    i.sle (midpoint i j) = true ∧ (i.slt j = true → (midpoint i j).slt j = true) := by
  unfold midpoint Go.convU
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide (config := {timeout := 120})

/-- SORT-SEARCH-MID-NAIVE (negative control): the naive `(i+j)/2` on signed `int` is *wrong*
for valid indices because `i+j` overflows; witness `i = 1`, `j = MaxInt`. -/
theorem midpoint_naive_refuted :
    ¬ ∀ i j : int, (0#64).sle i = true → i.sle j = true → ((i + j).sdiv 2) = midpoint i j := by
  intro h
  have := h 1 0x7FFFFFFFFFFFFFFF (by decide) (by decide)
  revert this; unfold midpoint Go.convU; decide

/-- No two adjacent elements are equal. -/
def NoAdjDup {α : Type} : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≠ b ∧ NoAdjDup (b :: rest)

/-- The first element of every run is kept: `Compact (a :: s)` starts with `a`. -/
theorem Compact_head {α : Type} [DecidableEq α] (a : α) (s : List α) :
    (Compact (a :: s)).head? = some a := by
  induction s generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [Compact]
    split
    · rename_i hab; subst hab; exact ih _
    · rfl

/-- SLICES-COMPACT-NOADJ: doc: "Compact replaces consecutive runs of equal elements with a
single copy." The result has no adjacent duplicates. -/
theorem Compact_noAdjDup {α : Type} [DecidableEq α] (s : List α) : NoAdjDup (Compact s) := by
  induction s with
  | nil => simp [Compact, NoAdjDup]
  | cons a rest ih =>
    cases rest with
    | nil => simp [Compact, NoAdjDup]
    | cons b rest' =>
      simp only [Compact]
      split
      · exact ih
      · rename_i hab
        have hhead := Compact_head b rest'
        revert ih hhead
        generalize Compact (b :: rest') = c
        intro ih hhead
        cases c with
        | nil => simp at hhead
        | cons c0 cs =>
          simp at hhead; subst hhead
          exact ⟨hab, ih⟩

/-- SLICES-COMPACT-SUBLIST: the result is a sublist of the input (nothing is invented). -/
theorem Compact_sublist {α : Type} [DecidableEq α] (s : List α) : (Compact s).Sublist s := by
  induction s with
  | nil => simp [Compact]
  | cons a rest ih =>
    cases rest with
    | nil => simp [Compact]
    | cons b rest' =>
      simp only [Compact]
      split
      · exact ih.cons a
      · exact ih.cons_cons a

/-- SLICES-COMPACT-LEN: the result is never longer than the input (the Go code returns `s[:k]`). -/
theorem Compact_length_le {α : Type} [DecidableEq α] (s : List α) : (Compact s).length ≤ s.length :=
  (Compact_sublist s).length_le

/-- SLICES-INDEX-SPEC: doc: "Index returns the index of the first occurrence of v in s, or -1 if
not present." -/
theorem indexFrom_spec {α : Type} [DecidableEq α] (v : α) (s : List α) (i : Nat) :
    (indexFrom v s i = -1 ↔ v ∉ s) ∧
    (∀ r : Nat, indexFrom v s i = r → i ≤ r ∧ s[r - i]? = some v ∧ ∀ k < r - i, s[k]? ≠ some v) := by
  induction s generalizing i with
  | nil => simp [indexFrom]
  | cons a t ih =>
    simp only [indexFrom]
    split
    · rename_i hav; subst hav
      constructor
      · constructor
        · intro h; omega
        · intro h; exact absurd (List.mem_cons_self ..) h
      · intro r hr
        have : r = i := by omega
        subst this
        refine ⟨Nat.le_refl _, by simp, fun k hk => by omega⟩
    · rename_i hav
      obtain ⟨ih1, ih2⟩ := ih (i + 1)
      constructor
      · rw [ih1]; simp [List.mem_cons]; intro h; exact fun h' => hav (h'.symm)
      · intro r hr
        obtain ⟨hle, hget, hbefore⟩ := ih2 r hr
        refine ⟨by omega, ?_, ?_⟩
        · have : r - i = (r - (i + 1)) + 1 := by omega
          rw [this]; simpa using hget
        · intro k hk
          cases k with
          | zero => simp; exact hav
          | succ k' =>
            have := hbefore k' (by omega)
            simpa using this

theorem Index_spec {α : Type} [DecidableEq α] (s : List α) (v : α) :
    (Index s v = -1 ↔ v ∉ s) ∧
    (∀ r : Nat, Index s v = r → s[r]? = some v ∧ ∀ k < r, s[k]? ≠ some v) := by
  obtain ⟨h1, h2⟩ := indexFrom_spec v s 0
  refine ⟨h1, fun r hr => ?_⟩
  obtain ⟨_, hget, hbefore⟩ := h2 r hr
  simpa using ⟨hget, hbefore⟩

/-- `indexFrom` is either `-1` or a non-negative index. -/
theorem indexFrom_neg_or_nonneg {α : Type} [DecidableEq α] (v : α) (t : List α) (i : Nat) :
    indexFrom v t i = -1 ∨ 0 ≤ indexFrom v t i := by
  induction t generalizing i with
  | nil => left; rfl
  | cons a t ih =>
    simp only [indexFrom]
    split
    · right; omega
    · exact ih (i + 1)

/-- SLICES-CONTAINS-SPEC: doc: "Contains reports whether v is present in s." -/
theorem Contains_spec {α : Type} [DecidableEq α] (s : List α) (v : α) : Contains s v = true ↔ v ∈ s := by
  unfold Contains
  obtain ⟨h1, _⟩ := Index_spec s v
  constructor
  · intro h
    rcases Decidable.em (v ∈ s) with hv | hv
    · exact hv
    · have : Index s v = -1 := h1.mpr hv
      simp [this] at h
  · intro hv
    rcases indexFrom_neg_or_nonneg v s 0 with h | h
    · exact absurd hv (h1.mp h)
    · unfold Index; simpa using h

/-- SORT-SEARCH-SPEC: doc: "Search uses binary search to find and return the smallest index i in
[0, n) at which f(i) is true, assuming that on the range [0, n), f(i) == true implies f(i+1) ==
true … If there is no such index, Search returns n." Loop invariant from search.go:60-61
(`f(i-1) == false, f(j) == true`), with `f(n)` taken as true. -/
theorem searchLoop_spec (f : Nat → Bool) (n : Nat) (mono : ∀ a b, a ≤ b → f a = true → f b = true)
    (i j : Nat) (hij : i ≤ j) (hjn : j ≤ n) (hi : ∀ k < i, f k = false) (hj : j < n → f j = true) :
    i ≤ searchLoop f i j ∧ searchLoop f i j ≤ j ∧
    (∀ k < searchLoop f i j, f k = false) ∧ (searchLoop f i j < n → f (searchLoop f i j) = true) := by
  induction i, j using searchLoop.induct f with
  | case1 i j hlt m hf ih =>
    have hm : m = (i + j) / 2 := rfl
    rw [searchLoop]; simp only [hlt, ↓reduceDIte]; rw [← hm]; simp only [hf, ↓reduceIte]
    have hmj : m < j := by omega
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) (by omega) hi (fun _ => hf)
    exact ⟨h1, by omega, h3, h4⟩
  | case2 i j hlt m hf ih =>
    have hm : m = (i + j) / 2 := rfl
    have hf' : f m = false := by simpa using hf
    rw [searchLoop]; simp only [hlt, ↓reduceDIte]; rw [← hm]; simp only [hf', Bool.false_eq_true, ↓reduceIte]
    have hi' : ∀ k < m + 1, f k = false := by
      intro k hk
      rcases Decidable.em (f k = true) with hk' | hk'
      · have : f m = true := mono k m (by omega) hk'
        simp [hf'] at this
      · simpa using hk'
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) hjn hi' hj
    exact ⟨by omega, h2, h3, h4⟩
  | case3 i j hnlt =>
    rw [searchLoop]; simp only [hnlt, ↓reduceDIte]
    have : i = j := by omega
    subst this
    exact ⟨Nat.le_refl _, Nat.le_refl _, hi, hj⟩

/-- SORT-SEARCH-SPEC (top level): for monotone `f` on `[0, n)`, `Search n f` is the smallest
index at which `f` is true, or `n` if there is none. -/
theorem Search_spec (f : Nat → Bool) (n : Nat) (mono : ∀ a b, a ≤ b → f a = true → f b = true) :
    Search n f ≤ n ∧ (∀ k < Search n f, f k = false) ∧ (Search n f < n → f (Search n f) = true) := by
  have := searchLoop_spec f n mono 0 n (Nat.zero_le _) (Nat.le_refl _) (fun k hk => absurd hk (Nat.not_lt_zero _))
    (fun h => absurd h (Nat.lt_irrefl _))
  unfold Search
  exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

end Go.Slices.Properties
