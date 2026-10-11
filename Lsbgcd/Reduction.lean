import Lsbgcd.ProofObligations

/-!
# Reduction to admissible words (the consequence of Theorem 4.3)

Assign digit 1 to steps with exponent zero and digit 2 to every other
step. Consecutive zero exponents are impossible. Replacing each inverse
step by the corresponding inverse A-step reduces the pair in `Smaller`.
-/
namespace Lsbgcd

theorem remainder_bounds {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    remainder u v + 2 ^ shift u v * v ≤ u ∧
      remainder u v + u ≤ 2 * (2 ^ shift u v * v) := by
  obtain ⟨hl, hu⟩ := shift_bounds hv hvu
  have h1 : remainder u v ≤ u - 2 ^ shift u v * v := min_le_left _ _
  have h2 : remainder u v ≤ 2 ^ (shift u v + 1) * v - u := min_le_right _ _
  rw [pow_succ', Nat.mul_assoc] at hu h2
  omega

theorem zero_shift_step {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u)
    (he : shift u v = 0) : 2 * (step u v).2 ≤ (step u v).1 := by
  obtain ⟨h1, h2⟩ := remainder_bounds hv hvu
  simp only [he, pow_zero, one_mul] at h1 h2
  have ht : remainder u v ≤ v := by omega
  simp only [step, max_eq_left ht, min_eq_right ht]
  omega

/-- Every actual step can be replaced by A₀ or A₁ on the same output pair. -/
theorem reduced_step_smaller {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    Smaller (inverseA (if shift u v = 0 then 0 else 1) (step u v)) (u, v) := by
  obtain ⟨h1, h2⟩ := remainder_bounds hv hvu
  by_cases he : shift u v = 0
  · simp only [he, pow_zero, one_mul] at h1 h2
    have ht : remainder u v ≤ v := by omega
    simp only [he, ↓reduceIte, Smaller, inverseA, step, max_eq_left ht,
      min_eq_right ht, pow_zero, one_mul]
    omega
  · have hp : 2 ≤ 2 ^ shift u v := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ shift u v by omega)
      simpa using this
    have hm : 2 * v ≤ 2 ^ shift u v * v := Nat.mul_le_mul_right v hp
    by_cases ht : remainder u v ≤ v
    · simp only [he, ↓reduceIte, Smaller, inverseA, step, max_eq_left ht,
        min_eq_right ht, pow_one]
      omega
    · have ht' : v ≤ remainder u v := by omega
      simp only [he, ↓reduceIte, Smaller, inverseA, step, max_eq_right ht',
        min_eq_left ht', pow_one]
      omega

def quotientWord (u v : ℕ) (_hvu : v ≤ u) : List ℕ :=
  if _hv : v = 0 then []
  else (if shift u v = 0 then 1 else 2) ::
    quotientWord (step u v).1 (step u v).2 (step_ordered u v)
termination_by u + v
decreasing_by exact step_decreases (Nat.pos_of_ne_zero _hv) _hvu

theorem quotientWord_head_one {u v : ℕ} (hvu : v ≤ u)
    (h : (quotientWord u v hvu).head? = some 1) : u < 2 * v := by
  rw [quotientWord] at h
  split_ifs at h with hv he
  · simp at h
  · have hi := (shift_bounds (Nat.pos_of_ne_zero hv) hvu).2
    simpa [he] using hi
  · simp at h

theorem quotientWord_admissible (u v : ℕ) (hvu : v ≤ u) :
    Admissible (quotientWord u v hvu) := by
  rw [quotientWord]
  split_ifs with hv he
  · trivial
  · have hi := quotientWord_admissible (step u v).1 (step u v).2 (step_ordered u v)
    have hz := zero_shift_step (Nat.pos_of_ne_zero hv) hvu he
    generalize hw : quotientWord (step u v).1 (step u v).2 (step_ordered u v) = as at hi ⊢
    cases as with
    | nil => exact Or.inl rfl
    | cons a as =>
      refine ⟨Or.inl rfl, ?_, hi⟩
      rintro ⟨_, ha⟩
      have hh : (quotientWord (step u v).1 (step u v).2 (step_ordered u v)).head? = some 1 := by
        simp [hw, ha]
      have := quotientWord_head_one (step_ordered u v) hh
      omega
  · exact admissible_two_cons
      (quotientWord_admissible (step u v).1 (step u v).2 (step_ordered u v))
termination_by u + v
decreasing_by all_goals exact step_decreases (Nat.pos_of_ne_zero hv) hvu

theorem quotientWord_length (u v : ℕ) (hvu : v ≤ u) :
    (quotientWord u v hvu).length = (run u v hvu).2 := by
  rw [quotientWord, run]
  by_cases hv : v = 0
  · simp [hv]
  · simp only [dite_eq_right hv, List.length_cons]
    simpa only using
      congrArg (fun n : ℕ => n + 1)
        (quotientWord_length (step u v).1 (step u v).2 (step_ordered u v))
termination_by u + v
decreasing_by exact step_decreases (Nat.pos_of_ne_zero hv) hvu

theorem quotientWord_smaller (u v : ℕ) (hu : 0 < u) (hvu : v ≤ u) :
    Smaller (convergent (quotientWord u v hvu)) (u, v) := by
  rw [quotientWord]
  split_ifs with hv he
  · simp only [convergent, Smaller]
    omega
  · have hn : 0 < (step u v).1 := lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (le_max_left _ _)
    have hi := quotientWord_smaller (step u v).1 (step u v).2 hn (step_ordered u v)
    have hs := reduced_step_smaller (Nat.pos_of_ne_zero hv) hvu
    simp only [he, ↓reduceIte] at hs
    have hm := smaller_trans (inverseA_mono 0 hi) hs
    simpa [he, inverseA, convergent] using hm
  · have hn : 0 < (step u v).1 := lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (le_max_left _ _)
    have hi := quotientWord_smaller (step u v).1 (step u v).2 hn (step_ordered u v)
    have hs := reduced_step_smaller (Nat.pos_of_ne_zero hv) hvu
    simp only [he, ↓reduceIte] at hs
    have hm := smaller_trans (inverseA_mono 1 hi) hs
    simpa [he, inverseA, convergent] using hm
termination_by u + v
decreasing_by all_goals exact step_decreases (Nat.pos_of_ne_zero hv) hvu

/-- The reduction needed from Theorem 4.3, proved for every input. -/
theorem reduction_to_admissible : ReductionToAdmissible := by
  intro u v hu hvu
  refine ⟨quotientWord u v hvu, quotientWord_admissible u v hvu, ?_,
    smaller_lex (quotientWord_smaller u v hu hvu)⟩
  rw [quotientWord_length, iterations_of_ordered hvu]

/-- The reduction step in Theorem 1.1; Minimality.lean supplies the
continuant-minimisation argument and obtains the unconditional result. -/
theorem main_of_admissible_minimality (h : AdmissibleMinimality) : MainTheorem :=
  main_of_reduction_and_minimality reduction_to_admissible h

end Lsbgcd
