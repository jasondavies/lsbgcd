module

public import Lsbgcd.Continuants

@[expose] public section

/-!
# Order and exchange facts for positive continuants

These facts apply to arbitrary positive integer digits. In particular,
unequal outside digits determine the sign of a word matrix's off-diagonal
difference. Equal outside digits reverse that sign. Together these are the
arithmetic ingredients for alternating comparisons of continuant words.
-/
namespace Lsbgcd

theorem positive_convergent {as : List ℕ} (h : ∀ a ∈ as, 0 < a) :
    0 < (convergent as).1 ∧ (convergent as).2 ≤ (convergent as).1 := by
  induction as with
  | nil => norm_num [convergent]
  | cons a as ih =>
    have ha := h a (by simp)
    obtain ⟨hp, hq⟩ := ih (fun b hb => h b (by simp [hb]))
    simp only [convergent]
    constructor <;> nlinarith

theorem positive_continuant {as : List ℕ} (h : ∀ a ∈ as, 0 < a) :
    0 < continuant as := (positive_convergent h).1

theorem positive_convergent_denominator {as : List ℕ}
    (h : ∀ a ∈ as, 0 < a) (hn : as ≠ []) : 0 < (convergent as).2 := by
  cases as with
  | nil => contradiction
  | cons a as => exact positive_continuant (fun b hb => h b (by simp [hb]))

theorem wordMatrix_nonnegative (as : List ℕ) (i j : Fin 2) :
    0 ≤ wordMatrix as i j := by
  induction as generalizing i j with
  | nil => simp [wordMatrix, Matrix.one_apply]; split_ifs <;> norm_num
  | cons a as ih =>
    have h00 := ih 0 0
    have h01 := ih 0 1
    have h10 := ih 1 0
    have h11 := ih 1 1
    fin_cases i <;> fin_cases j <;>
      simp [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
      positivity

theorem wordMatrix_upper_right_positive {as : List ℕ}
    (h : ∀ a ∈ as, 0 < a) (hn : as ≠ []) : 0 < wordMatrix as 0 1 := by
  have hr : ∀ a ∈ as.reverse, 0 < a := by simpa using h
  have hp := positive_convergent_denominator hr (by simpa using hn)
  have hm := (wordMatrix_first_column as.reverse).2
  rw [wordMatrix_reverse] at hm
  simp only [Matrix.transpose_apply] at hm
  rw [hm]
  exact_mod_cast hp

/-- Strict comparison of the two one-ended continuants, determined by
unequal outside digits. No restriction to the binary alphabet is needed. -/
theorem wordMatrix_endpoints_strict {as : List ℕ} {x y : ℕ}
    (h : ∀ a ∈ as, 0 < a) (hxy : x < y) :
    wordMatrix (x :: (as ++ [y])) 0 1 < wordMatrix (x :: (as ++ [y])) 1 0 := by
  have hconv := positive_convergent h
  have h00 : 0 < wordMatrix as 0 0 := by
    rw [(wordMatrix_first_column as).1]
    exact_mod_cast hconv.1
  have h10 : wordMatrix as 1 0 ≤ wordMatrix as 0 0 := by
    rw [(wordMatrix_first_column as).1, (wordMatrix_first_column as).2]
    exact_mod_cast hconv.2
  have hxy' : (x : ℤ) + 1 ≤ y := by exact_mod_cast hxy
  by_cases hn : as = []
  · subst as
    simpa [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      (show (x : ℤ) < y by exact_mod_cast hxy)
  · have h01 := wordMatrix_upper_right_positive h hn
    simp only [wordMatrix, wordMatrix_append, mul_one, digitMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_zero, mul_one, one_mul, zero_mul, add_zero]
    nlinarith

/-- Equal outside digits reverse the off-diagonal difference. -/
theorem wordMatrix_equal_endpoints (as : List ℕ) (a : ℕ) :
    wordMatrix (a :: (as ++ [a])) 0 1 - wordMatrix (a :: (as ++ [a])) 1 0 =
      -(wordMatrix as 0 1 - wordMatrix as 1 0) := by
  simp only [wordMatrix, wordMatrix_append, mul_one, digitMatrix,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, mul_one, one_mul, zero_mul, add_zero]
  ring

end Lsbgcd
