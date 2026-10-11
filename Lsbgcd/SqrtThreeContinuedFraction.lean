import Lsbgcd.SumSquares
import Lsbgcd.PaperCorollaries

/-!
# The continued-fraction bridge for the sum-of-squares conjecture

The truncations `[1; 1,2,1,2,…]` converge to `√3`. Their denominators,
after skipping the first convergent, are the recurrence terms used in the
sum-of-squares theorem. The proof gives an explicit geometric error bound.
-/
namespace Lsbgcd

open Filter

/-- The prefix `[1; 1,2,1,2,…]` with `n` entries after the semicolon. -/
def sqrtThreeWord (n : ℕ) : List ℕ :=
  1 :: (List.range n).map (fun k => if k % 2 = 0 then 1 else 2)

/-- The real value of the `n`th finite continued fraction, starting with `1`. -/
noncomputable def sqrtThreeConvergent (n : ℕ) : ℝ :=
  (convergent (sqrtThreeWord n)).1 / (convergent (sqrtThreeWord n)).2

private theorem sqrtThreeWord_positive (n : ℕ) :
    ∀ a ∈ sqrtThreeWord n, 0 < a := by
  intro a ha
  simp only [sqrtThreeWord, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨k, _, rfl⟩
  · decide
  · split_ifs <;> decide

/-- Connect the real-valued approximants to the paper's rational CF evaluator. -/
theorem sqrtThreeConvergent_eq_continuedFraction (n : ℕ) :
    sqrtThreeConvergent n = (continuedFraction (sqrtThreeWord n) : ℝ) := by
  rw [continuedFraction_eq_convergent (sqrtThreeWord_positive n)]
  simp [sqrtThreeConvergent]

/-- The precise indexing of the denominator sequence from the conjecture. -/
theorem sqrtThreeConvergent_denominator (n : ℕ) :
    (convergent (sqrtThreeWord (n + 1))).2 = squareNumerator n :=
  squareNumerator_sqrtThree_denominator n

private theorem sqrtThree_tail_add_two (n : ℕ) :
    (List.range (n + 2)).map (fun k => if k % 2 = 0 then 1 else 2) =
      1 :: 2 :: (List.range n).map (fun k => if k % 2 = 0 then 1 else 2) := by
  rw [show n + 2 = 2 + n by omega, List.range_add]
  norm_num [List.map_map, Function.comp_def, List.range_succ]

/-- Advancing by one period acts by the Pell matrix `[[2,3],[1,2]]`. -/
theorem sqrtThreeConvergent_pair_add_two (n : ℕ) :
    convergent (sqrtThreeWord (n + 2)) =
      (2 * (convergent (sqrtThreeWord n)).1 + 3 * (convergent (sqrtThreeWord n)).2,
       (convergent (sqrtThreeWord n)).1 + 2 * (convergent (sqrtThreeWord n)).2) := by
  simp only [sqrtThreeWord, sqrtThree_tail_add_two, convergent]
  congr 1 <;> ring

theorem sqrtThreeConvergent_ge_one (n : ℕ) : 1 ≤ sqrtThreeConvergent n := by
  have hp := positive_convergent (sqrtThreeWord_positive n)
  have hq := positive_convergent_denominator (sqrtThreeWord_positive n)
    (by simp [sqrtThreeWord])
  unfold sqrtThreeConvergent
  apply (le_div_iff₀ (by exact_mod_cast hq)).2
  simpa using (show ((convergent (sqrtThreeWord n)).2 : ℝ) ≤
    (convergent (sqrtThreeWord n)).1 by exact_mod_cast hp.2)

/-- The two-step recurrence on the values of the continued fractions. -/
theorem sqrtThreeConvergent_add_two (n : ℕ) :
    sqrtThreeConvergent (n + 2) =
      (2 * sqrtThreeConvergent n + 3) / (sqrtThreeConvergent n + 2) := by
  have hq := positive_convergent_denominator (sqrtThreeWord_positive n)
    (by simp [sqrtThreeWord])
  have hq0 : ((convergent (sqrtThreeWord n)).2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  unfold sqrtThreeConvergent
  rw [sqrtThreeConvergent_pair_add_two]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private theorem sqrtThree_bounds : 1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hpos := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

private theorem sqrtThree_mobius_contract {x : ℝ} (hx : 1 ≤ x) :
    |(2 * x + 3) / (x + 2) - Real.sqrt 3| ≤ 1 / 3 * |x - Real.sqrt 3| := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  obtain ⟨hs1, hs2⟩ := sqrtThree_bounds
  have hd : 0 < x + 2 := by linarith
  have he : (2 * x + 3) / (x + 2) - Real.sqrt 3 =
      (2 - Real.sqrt 3) / (x + 2) * (x - Real.sqrt 3) := by
    field_simp
    nlinarith
  rw [he, abs_mul, abs_of_nonneg (div_nonneg (by linarith) hd.le)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply (div_le_iff₀ hd).2
  linarith

/-- Each pair of new partial quotients reduces the error by at least a factor of 3. -/
theorem sqrtThreeConvergent_error (n : ℕ) :
    |sqrtThreeConvergent n - Real.sqrt 3| ≤ (1 / 3 : ℝ) ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · obtain ⟨hs1, hs2⟩ := sqrtThree_bounds
      norm_num [sqrtThreeConvergent, sqrtThreeWord, convergent]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · obtain ⟨hs1, hs2⟩ := sqrtThree_bounds
      norm_num [sqrtThreeConvergent, sqrtThreeWord, convergent]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [sqrtThreeConvergent_add_two]
      calc
        _ ≤ 1 / 3 * |sqrtThreeConvergent n - Real.sqrt 3| :=
          sqrtThree_mobius_contract (sqrtThreeConvergent_ge_one n)
        _ ≤ 1 / 3 * (1 / 3 : ℝ) ^ (n / 2) :=
          mul_le_mul_of_nonneg_left (ih n (by omega)) (by norm_num)
        _ = (1 / 3 : ℝ) ^ ((n + 2) / 2) := by
          rw [show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
          ring

/-- The infinite continued fraction `[1; 1,2,1,2,…]` has value `√3`. -/
theorem sqrtThreeConvergent_tendsto :
    Tendsto sqrtThreeConvergent atTop (nhds (Real.sqrt 3)) := by
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => by omega⟩
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)).comp hdiv
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) sqrtThreeConvergent_error hpow

/-- The same limit stated directly for the finite continued-fraction expressions. -/
theorem sqrtThree_continuedFraction_tendsto :
    Tendsto (fun n => (continuedFraction (sqrtThreeWord n) : ℝ))
      atTop (nhds (Real.sqrt 3)) := by
  convert sqrtThreeConvergent_tendsto using 1
  funext n
  exact (sqrtThreeConvergent_eq_continuedFraction n).symm

end Lsbgcd
