module

public import Lsbgcd.Words
public import Lsbgcd.Recurrences

@[expose] public section

/-!
# The worst-case input sequences (§§5–6)

These definitions construct the words selected in §6, including the
lexicographic tie-break for lengths congruent to 2 modulo 4. This module
proves their admissibility and iteration counts. Their global minimality
is proved in Minimality.lean.
-/
namespace Lsbgcd

def repeat12 : ℕ → List ℕ
  | 0 => []
  | n + 1 => 1 :: 2 :: repeat12 n

def repeat21 : ℕ → List ℕ
  | 0 => []
  | n + 1 => 2 :: 1 :: repeat21 n

theorem admissible_two_cons {as : List ℕ} (h : Admissible as) : Admissible (2 :: as) := by
  cases as with
  | nil => simp [Admissible]
  | cons a as => simpa [Admissible] using h

theorem admissible_one_two_cons {as : List ℕ} (h : Admissible as) :
    Admissible (1 :: 2 :: as) := by
  exact ⟨Or.inl rfl, by decide, admissible_two_cons h⟩

theorem admissible_repeat12_append {as : List ℕ} (n : ℕ) (h : Admissible as) :
    Admissible (repeat12 n ++ as) := by
  induction n with
  | zero => exact h
  | succ n ih => exact admissible_one_two_cons ih

theorem admissible_repeat21 (n : ℕ) : Admissible (repeat21 n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases n with
    | zero => simp [repeat21, Admissible]
    | succ n => exact admissible_two_cons (admissible_one_two_cons (admissible_tail ih))

@[simp] theorem length_repeat12 (n : ℕ) : (repeat12 n).length = 2 * n := by
  induction n <;> simp_all [repeat12]; omega

@[simp] theorem length_repeat21 (n : ℕ) : (repeat21 n).length = 2 * n := by
  induction n <;> simp_all [repeat21]; omega

def candidateWord (n : ℕ) : List ℕ :=
  if n % 2 = 1 then repeat12 (n / 2) ++ [1]
  else if n % 4 = 0 then repeat12 (n / 4) ++ repeat21 (n / 4)
  else repeat12 (n / 4) ++ repeat21 (n / 4 + 1)

def candidate (n : ℕ) : ℕ × ℕ := convergent (candidateWord n)

theorem candidateWord_admissible (n : ℕ) : Admissible (candidateWord n) := by
  unfold candidateWord
  split_ifs
  · exact admissible_repeat12_append _ (Or.inl rfl)
  · exact admissible_repeat12_append _ (admissible_repeat21 _)
  · exact admissible_repeat12_append _ (admissible_repeat21 _)

theorem candidateWord_length (n : ℕ) : (candidateWord n).length = n := by
  unfold candidateWord
  split_ifs with h1 h2 <;> simp only [List.length_append, length_repeat12,
    length_repeat21, List.length_cons, List.length_nil] <;> omega

/-- The candidate inputs really require exactly n iterations, for all n. -/
theorem candidate_iterations (n : ℕ) : iterations (candidate n).1 (candidate n).2 = n := by
  rw [candidate, admissible_iterations (candidateWord_admissible n), candidateWord_length]

theorem candidate_positive_ordered (n : ℕ) :
    0 < (candidate n).1 ∧ (candidate n).2 ≤ (candidate n).1 :=
  admissible_convergent (candidateWord_admissible n)

theorem candidate_coprime (n : ℕ) : Nat.Coprime (candidate n).1 (candidate n).2 :=
  convergent_coprime _

theorem wordMatrix_repeat12 (n : ℕ) : wordMatrix (repeat12 n) = (m1 * m2) ^ n := by
  induction n with
  | zero => simp [repeat12, wordMatrix]
  | succ n ih => simp [repeat12, wordMatrix, ih, pow_succ', m1, m2, Matrix.mul_assoc]

theorem wordMatrix_repeat21 (n : ℕ) : wordMatrix (repeat21 n) = (m2 * m1) ^ n := by
  induction n with
  | zero => simp [repeat21, wordMatrix]
  | succ n ih => simp [repeat21, wordMatrix, ih, pow_succ', m1, m2, Matrix.mul_assoc]

theorem candidate_even_matrix (n : ℕ) :
    (candidate (4 * n)).1 = evenMatrix n 0 0 ∧
      (candidate (4 * n)).2 = evenMatrix n 1 0 := by
  have hw : candidateWord (4 * n) = repeat12 n ++ repeat21 n := by
    simp [candidateWord, Nat.mul_mod]
  have h := wordMatrix_first_column (repeat12 n ++ repeat21 n)
  rw [wordMatrix_append, wordMatrix_repeat12, wordMatrix_repeat21, ← evenMatrix_powers] at h
  simpa [candidate, hw] using And.intro h.1.symm h.2.symm

theorem candidate_offset_matrix (n : ℕ) :
    (candidate (4 * n + 2)).1 = offsetMatrix n 0 0 ∧
      (candidate (4 * n + 2)).2 = offsetMatrix n 1 0 := by
  have hw : candidateWord (4 * n + 2) = repeat12 n ++ repeat21 (n + 1) := by
    simp [candidateWord, Nat.add_div, Nat.add_mod, Nat.mul_mod]
  have h := wordMatrix_first_column (repeat12 n ++ repeat21 (n + 1))
  rw [wordMatrix_append, wordMatrix_repeat12, wordMatrix_repeat21, ← offsetMatrix_powers] at h
  simpa [candidate, hw] using And.intro h.1.symm h.2.symm

theorem candidate_odd_word (n : ℕ) :
    candidate (2 * n + 1) = convergent (repeat12 n ++ [1]) := by
  simp [candidate, candidateWord, Nat.add_mod, Nat.add_div]

/-- The second-order recurrence in §6, case (i), written without subtraction. -/
theorem candidate_odd_recurrence (n : ℕ) :
    (candidate (2 * (n + 2) + 1)).1 + (candidate (2 * n + 1)).1 =
      4 * (candidate (2 * (n + 1) + 1)).1 ∧
    (candidate (2 * (n + 2) + 1)).2 + (candidate (2 * n + 1)).2 =
      4 * (candidate (2 * (n + 1) + 1)).2 := by
  simp only [candidate_odd_word, repeat12, List.cons_append, convergent]
  constructor <;> ring

/-- The even subsequence recurrence in §6, case (ii). -/
theorem candidate_even_recurrence (n : ℕ) :
    (candidate (4 * (n + 3))).1 + 15 * (candidate (4 * (n + 1))).1 =
      15 * (candidate (4 * (n + 2))).1 + (candidate (4 * n)).1 ∧
    (candidate (4 * (n + 3))).2 + 15 * (candidate (4 * (n + 1))).2 =
      15 * (candidate (4 * (n + 2))).2 + (candidate (4 * n)).2 := by
  have hm := orbit_recurrence (1 : Mat) n
  have h0 := congrArg (fun m : Mat => m 0 0) hm
  have h1 := congrArg (fun m : Mat => m 1 0) hm
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h0 h1
  change evenMatrix (n + 3) 0 0 = 15 * evenMatrix (n + 2) 0 0 -
    15 * evenMatrix (n + 1) 0 0 + evenMatrix n 0 0 at h0
  change evenMatrix (n + 3) 1 0 = 15 * evenMatrix (n + 2) 1 0 -
    15 * evenMatrix (n + 1) 1 0 + evenMatrix n 1 0 at h1
  simp only [← (candidate_even_matrix _).1] at h0
  simp only [← (candidate_even_matrix _).2] at h1
  constructor <;> omega

/-- The even subsequence recurrence in §6, case (iii). -/
theorem candidate_offset_recurrence (n : ℕ) :
    (candidate (4 * (n + 3) + 2)).1 + 15 * (candidate (4 * (n + 1) + 2)).1 =
      15 * (candidate (4 * (n + 2) + 2)).1 + (candidate (4 * n + 2)).1 ∧
    (candidate (4 * (n + 3) + 2)).2 + 15 * (candidate (4 * (n + 1) + 2)).2 =
      15 * (candidate (4 * (n + 2) + 2)).2 + (candidate (4 * n + 2)).2 := by
  have hm := orbit_recurrence (m2 * m1) n
  have h0 := congrArg (fun m : Mat => m 0 0) hm
  have h1 := congrArg (fun m : Mat => m 1 0) hm
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h0 h1
  change offsetMatrix (n + 3) 0 0 = 15 * offsetMatrix (n + 2) 0 0 -
    15 * offsetMatrix (n + 1) 0 0 + offsetMatrix n 0 0 at h0
  change offsetMatrix (n + 3) 1 0 = 15 * offsetMatrix (n + 2) 1 0 -
    15 * offsetMatrix (n + 1) 1 0 + offsetMatrix n 1 0 at h1
  simp only [← (candidate_offset_matrix _).1] at h0
  simp only [← (candidate_offset_matrix _).2] at h1
  constructor <;> omega

end Lsbgcd
