import Lsbgcd.ContinuantOrder

/-!
# Weighted continuants for the Ramharter induction

The rational parameters retain the contribution from the already fixed
outside digits. Peeling endpoints reciprocates their updated parameters.
-/
namespace Lsbgcd

/-- The bilinear form `[1,l] M(w) [1,r]ᵀ`. -/
def weightedContinuant (l r : ℚ) (w : List ℕ) : ℚ :=
  (wordMatrix w 0 0 : ℚ) + l * (wordMatrix w 1 0 : ℚ) +
    r * (wordMatrix w 0 1 : ℚ) + l * r * (wordMatrix w 1 1 : ℚ)

@[simp] theorem weightedContinuant_zero (w : List ℕ) :
    weightedContinuant 0 0 w = (continuant w : ℚ) := by
  simp only [weightedContinuant, zero_mul, add_zero]
  rw [(wordMatrix_first_column w).1]
  norm_cast

@[simp] theorem weightedContinuant_nil (l r : ℚ) :
    weightedContinuant l r [] = 1 + l * r := by
  norm_num [weightedContinuant, wordMatrix]

@[simp] theorem weightedContinuant_singleton (l r : ℚ) (a : ℕ) :
    weightedContinuant l r [a] = a + l + r := by
  norm_num [weightedContinuant, wordMatrix, digitMatrix]

theorem weightedContinuant_reverse (l r : ℚ) (w : List ℕ) :
    weightedContinuant l r w.reverse = weightedContinuant r l w := by
  simp only [weightedContinuant, wordMatrix_reverse, Matrix.transpose_apply]
  ring

theorem weightedContinuant_nonnegative {l r : ℚ} (w : List ℕ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) : 0 ≤ weightedContinuant l r w := by
  have h00 : (0 : ℚ) ≤ wordMatrix w 0 0 := by exact_mod_cast wordMatrix_nonnegative w 0 0
  have h01 : (0 : ℚ) ≤ wordMatrix w 0 1 := by exact_mod_cast wordMatrix_nonnegative w 0 1
  have h10 : (0 : ℚ) ≤ wordMatrix w 1 0 := by exact_mod_cast wordMatrix_nonnegative w 1 0
  have h11 : (0 : ℚ) ≤ wordMatrix w 1 1 := by exact_mod_cast wordMatrix_nonnegative w 1 1
  unfold weightedContinuant
  positivity

theorem weightedContinuant_positive {l r : ℚ} {w : List ℕ}
    (hl : 0 ≤ l) (hr : 0 ≤ r) (hw : ∀ a ∈ w, 0 < a) :
    0 < weightedContinuant l r w := by
  have h00 : (0 : ℚ) < wordMatrix w 0 0 := by
    rw [(wordMatrix_first_column w).1]
    exact_mod_cast (positive_convergent hw).1
  have h01 : (0 : ℚ) ≤ wordMatrix w 0 1 := by exact_mod_cast wordMatrix_nonnegative w 0 1
  have h10 : (0 : ℚ) ≤ wordMatrix w 1 0 := by exact_mod_cast wordMatrix_nonnegative w 1 0
  have h11 : (0 : ℚ) ≤ wordMatrix w 1 1 := by exact_mod_cast wordMatrix_nonnegative w 1 1
  unfold weightedContinuant
  positivity

/-- Factoring the two positive endpoint contributions leaves the same
weighted objective with reciprocal parameters on the interior word. -/
theorem weightedContinuant_peel {l r : ℚ} {a b : ℕ} (w : List ℕ)
    (ha : (a : ℚ) + l ≠ 0) (hb : (b : ℚ) + r ≠ 0) :
    weightedContinuant l r (a :: (w ++ [b])) =
      ((a : ℚ) + l) * ((b : ℚ) + r) *
        weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) w := by
  simp only [weightedContinuant, wordMatrix, wordMatrix_append, mul_one, digitMatrix,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Int.cast_one, Int.cast_zero]
  field_simp
  ring

theorem weightedContinuant_peel_pos {l r : ℚ} {a b : ℕ} (w : List ℕ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    weightedContinuant l r (a :: (w ++ [b])) =
      ((a : ℚ) + l) * ((b : ℚ) + r) *
        weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) w := by
  apply weightedContinuant_peel
  · have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    linarith
  · have hb' : (0 : ℚ) < b := by exact_mod_cast hb
    linarith

/-- With fixed positive endpoints, minimising the full word is equivalent
to minimising its interior under the updated boundary parameters. -/
theorem weightedContinuant_peel_le_iff {l r : ℚ} {a b : ℕ} (u v : List ℕ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    weightedContinuant l r (a :: (u ++ [b])) ≤
        weightedContinuant l r (a :: (v ++ [b])) ↔
      weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) u ≤
        weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) v := by
  rw [weightedContinuant_peel_pos u hl hr ha hb, weightedContinuant_peel_pos v hl hr ha hb]
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hf : 0 < ((a : ℚ) + l) * ((b : ℚ) + r) := by positivity
  exact mul_le_mul_iff_right₀ hf

/-- The positive endpoint factor also preserves the equality cases. -/
theorem weightedContinuant_peel_eq_iff {l r : ℚ} {a b : ℕ} (u v : List ℕ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    weightedContinuant l r (a :: (u ++ [b])) =
        weightedContinuant l r (a :: (v ++ [b])) ↔
      weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) u =
        weightedContinuant (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) v := by
  rw [weightedContinuant_peel_pos u hl hr ha hb, weightedContinuant_peel_pos v hl hr ha hb]
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hf : 0 < ((a : ℚ) + l) * ((b : ℚ) + r) := by positivity
  constructor
  · exact mul_left_cancel₀ (ne_of_gt hf)
  · intro h
    rw [h]

/-- The complete interval-reversal exchange identity for the weighted
objective. The unweighted identity is its specialization at zero parameters. -/
theorem weightedContinuant_reverse_interval_difference (l r : ℚ) (as bs cs : List ℕ) :
    weightedContinuant l r (as ++ bs ++ cs) -
      weightedContinuant l r (as ++ bs.reverse ++ cs) =
      ((wordMatrix bs 0 1 : ℚ) - (wordMatrix bs 1 0 : ℚ)) *
        (((wordMatrix as 0 0 : ℚ) + l * (wordMatrix as 1 0 : ℚ)) *
            ((wordMatrix cs 1 0 : ℚ) + r * (wordMatrix cs 1 1 : ℚ)) -
          ((wordMatrix as 0 1 : ℚ) + l * (wordMatrix as 1 1 : ℚ)) *
            ((wordMatrix cs 0 0 : ℚ) + r * (wordMatrix cs 0 1 : ℚ))) := by
  simp only [weightedContinuant, wordMatrix_append, wordMatrix_reverse,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Int.cast_add, Int.cast_mul]
  ring

/-- Prefix reversal compares the interval skew with the weighted rational
boundary contributed by the remaining suffix. -/
theorem weightedContinuant_reverse_prefix_difference (l r : ℚ) (bs cs : List ℕ) :
    weightedContinuant l r (bs ++ cs) - weightedContinuant l r (bs.reverse ++ cs) =
      ((wordMatrix bs 0 1 : ℚ) - (wordMatrix bs 1 0 : ℚ)) *
        (((wordMatrix cs 1 0 : ℚ) + r * (wordMatrix cs 1 1 : ℚ)) -
          l * ((wordMatrix cs 0 0 : ℚ) + r * (wordMatrix cs 0 1 : ℚ))) := by
  simpa [wordMatrix] using weightedContinuant_reverse_interval_difference l r [] bs cs

/-- The symmetric suffix-reversal exchange identity. -/
theorem weightedContinuant_reverse_suffix_difference (l r : ℚ) (as bs : List ℕ) :
    weightedContinuant l r (as ++ bs) - weightedContinuant l r (as ++ bs.reverse) =
      ((wordMatrix bs 0 1 : ℚ) - (wordMatrix bs 1 0 : ℚ)) *
        (r * ((wordMatrix as 0 0 : ℚ) + l * (wordMatrix as 1 0 : ℚ)) -
          ((wordMatrix as 0 1 : ℚ) + l * (wordMatrix as 1 1 : ℚ))) := by
  simpa [wordMatrix, mul_comm r] using
    weightedContinuant_reverse_interval_difference l r as bs []

/-- Whole-word reversal is governed by the boundary order and matrix skew. -/
theorem weightedContinuant_reverse_difference (l r : ℚ) (w : List ℕ) :
    weightedContinuant l r w - weightedContinuant l r w.reverse =
      (r - l) * ((wordMatrix w 0 1 : ℚ) - (wordMatrix w 1 0 : ℚ)) := by
  rw [weightedContinuant_reverse]
  unfold weightedContinuant
  ring

theorem weightedContinuant_reverse_equal_boundary (l : ℚ) (w : List ℕ) :
    weightedContinuant l l w.reverse = weightedContinuant l l w :=
  weightedContinuant_reverse l l w

private theorem endpoint_skew_positive {a b : ℕ} {mid : List ℕ}
    (hpos : ∀ x ∈ mid, 0 < x) (hba : b < a) :
    (0 : ℚ) < (wordMatrix (a :: (mid ++ [b])) 0 1 : ℚ) -
      (wordMatrix (a :: (mid ++ [b])) 1 0 : ℚ) := by
  have hs := wordMatrix_endpoints_strict (as := mid.reverse)
    (by simpa using hpos) hba
  have he : b :: (mid.reverse ++ [a]) = (a :: (mid ++ [b])).reverse := by simp
  rw [he, wordMatrix_reverse] at hs
  simp only [Matrix.transpose_apply] at hs
  exact_mod_cast sub_pos.mpr hs

theorem weightedContinuant_low_reverse_lt {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hlr : l < r) (hba : b < a) :
    weightedContinuant l r (a :: (mid ++ [b])).reverse <
      weightedContinuant l r (a :: (mid ++ [b])) := by
  have hp := mul_pos (sub_pos.mpr hlr) (endpoint_skew_positive hpos hba)
  rw [← weightedContinuant_reverse_difference] at hp
  exact sub_pos.mp hp

theorem weightedContinuant_high_reverse_lt {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hrl : r < l) (hab : a < b) :
    weightedContinuant l r (a :: (mid ++ [b])).reverse <
      weightedContinuant l r (a :: (mid ++ [b])) := by
  have hs := wordMatrix_endpoints_strict hpos hab
  have hsq : (wordMatrix (a :: (mid ++ [b])) 0 1 : ℚ) -
      (wordMatrix (a :: (mid ++ [b])) 1 0 : ℚ) < 0 := by
    exact_mod_cast sub_neg.mpr hs
  have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hrl) hsq
  rw [← weightedContinuant_reverse_difference] at hp
  exact sub_pos.mp hp

theorem weightedContinuant_low_reverse_le {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hlr : l ≤ r) (hba : b < a) :
    weightedContinuant l r (a :: (mid ++ [b])).reverse ≤
      weightedContinuant l r (a :: (mid ++ [b])) := by
  rcases eq_or_lt_of_le hlr with he | he
  · subst r
    exact le_of_eq (weightedContinuant_reverse_equal_boundary _ _)
  · exact le_of_lt (weightedContinuant_low_reverse_lt mid hpos he hba)

theorem weightedContinuant_high_reverse_le {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hrl : r ≤ l) (hab : a < b) :
    weightedContinuant l r (a :: (mid ++ [b])).reverse ≤
      weightedContinuant l r (a :: (mid ++ [b])) := by
  rcases eq_or_lt_of_le hrl with he | he
  · subst l
    exact le_of_eq (weightedContinuant_reverse_equal_boundary _ _)
  · exact le_of_lt (weightedContinuant_high_reverse_lt mid hpos he hab)

/-- A minimum is oriented increasingly at low unequal boundaries. Equal
boundaries are exactly the case in which reversing preserves the objective. -/
theorem weightedContinuant_low_endpoint_order {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hlr : l ≤ r)
    (hmin : weightedContinuant l r (a :: (mid ++ [b])) ≤
      weightedContinuant l r (a :: (mid ++ [b])).reverse) : a ≤ b ∨ l = r := by
  by_cases hab : a ≤ b
  · exact Or.inl hab
  · right
    by_contra hne
    have hs := weightedContinuant_low_reverse_lt (a := a) (b := b) mid hpos
      (lt_of_le_of_ne hlr hne) (by omega)
    exact (not_lt_of_ge hmin) hs

/-- The corresponding decreasing orientation at high unequal boundaries. -/
theorem weightedContinuant_high_endpoint_order {l r : ℚ} {a b : ℕ} (mid : List ℕ)
    (hpos : ∀ x ∈ mid, 0 < x) (hrl : r ≤ l)
    (hmin : weightedContinuant l r (a :: (mid ++ [b])) ≤
      weightedContinuant l r (a :: (mid ++ [b])).reverse) : b ≤ a ∨ l = r := by
  by_cases hba : b ≤ a
  · exact Or.inl hba
  · right
    by_contra hne
    have hs := weightedContinuant_high_reverse_lt (a := a) (b := b) mid hpos
      (lt_of_le_of_ne hrl (Ne.symm hne)) (by omega)
    exact (not_lt_of_ge hmin) hs

end Lsbgcd
