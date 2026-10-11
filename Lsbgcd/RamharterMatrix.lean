import Lsbgcd.RamharterBoundary

/-! # Matrix evaluation of continued fractions with a rational boundary -/
namespace Lsbgcd

/-- The denominator after attaching a nonnegative right boundary is positive
for every word of positive digits, including the empty word. -/
theorem boundary_matrix_denominator_pos {as : List ℕ} {r : ℚ}
    (h : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) :
    0 < (wordMatrix as 0 0 : ℚ) + (wordMatrix as 0 1 : ℚ) * r := by
  have h00 : 0 < (wordMatrix as 0 0 : ℚ) := by
    rw [(wordMatrix_first_column as).1]
    exact_mod_cast (positive_convergent h).1
  have h01 : 0 ≤ (wordMatrix as 0 1 : ℚ) := by
    exact_mod_cast wordMatrix_nonnegative as 0 1
  positivity

/-- A finite continued fraction with a rational tail is the linear
fractional transformation represented by its continuant matrix. -/
theorem boundaryCF_eq_matrix {as : List ℕ} {r : ℚ}
    (h : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) :
    boundaryCF as r =
      ((wordMatrix as 1 0 : ℚ) + (wordMatrix as 1 1 : ℚ) * r) /
      ((wordMatrix as 0 0 : ℚ) + (wordMatrix as 0 1 : ℚ) * r) := by
  induction as with
  | nil => simp [boundaryCF, wordMatrix]
  | cons a as ih =>
    have ht : ∀ b ∈ as, 0 < b := fun b hb => h b (by simp [hb])
    have hd := boundary_matrix_denominator_pos ht hr
    rw [boundaryCF, ih ht]
    simp only [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [add_div' _ _ _ (ne_of_gt hd), one_div_div]
    congr 1
    ring

/-- The sign of a matrix boundary factor is exactly a comparison of the
two rational continued-fraction boundary values. -/
theorem boundary_matrix_compare {as : List ℕ} {l r : ℚ}
    (h : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) :
    l < boundaryCF as r ↔
      0 < (wordMatrix as 1 0 : ℚ) + (wordMatrix as 1 1 : ℚ) * r -
        l * ((wordMatrix as 0 0 : ℚ) + (wordMatrix as 0 1 : ℚ) * r) := by
  rw [boundaryCF_eq_matrix h hr, lt_div_iff₀ (boundary_matrix_denominator_pos h hr)]
  exact sub_pos.symm

theorem boundary_matrix_compare_rev {as : List ℕ} {l r : ℚ}
    (h : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) :
    boundaryCF as r < l ↔
      (wordMatrix as 1 0 : ℚ) + (wordMatrix as 1 1 : ℚ) * r -
        l * ((wordMatrix as 0 0 : ℚ) + (wordMatrix as 0 1 : ℚ) * r) < 0 := by
  rw [boundaryCF_eq_matrix h hr, div_lt_iff₀ (boundary_matrix_denominator_pos h hr)]
  exact sub_neg.symm

theorem boundary_matrix_eq {as : List ℕ} {l r : ℚ}
    (h : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) :
    l = boundaryCF as r ↔
      (wordMatrix as 1 0 : ℚ) + (wordMatrix as 1 1 : ℚ) * r -
        l * ((wordMatrix as 0 0 : ℚ) + (wordMatrix as 0 1 : ℚ) * r) = 0 := by
  rw [boundaryCF_eq_matrix h hr,
    eq_div_iff (ne_of_gt (boundary_matrix_denominator_pos h hr))]
  exact eq_comm.trans sub_eq_zero.symm

end Lsbgcd
