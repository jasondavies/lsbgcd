module

public import Lsbgcd.SharpComplexity

@[expose] public section

/-!
# The Euclidean comparison in §7

Division steps are counted in the ordinary Euclidean algorithm. Consecutive
Fibonacci numbers are its least inputs for at least two divisions. The
one-division case under the paper's non-strict input order is `(1,1)`;
under strict input order it is `(2,1)`. Keeping this boundary explicit avoids
extending the quoted Fibonacci description beyond its valid range.
-/
namespace Lsbgcd

open Filter

/-- Number of divisions in the ordinary Euclidean algorithm. -/
def euclidSteps (u v : ℕ) : ℕ :=
  if hv : v = 0 then 0 else euclidSteps v (u % v) + 1
termination_by v
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hv)

@[simp] theorem euclidSteps_zero (u : ℕ) : euclidSteps u 0 = 0 := by
  rw [euclidSteps, dite_eq_left rfl]

theorem euclidSteps_same {u : ℕ} (hu : 0 < u) : euclidSteps u u = 1 := by
  rw [euclidSteps, dite_eq_right (ne_of_gt hu), Nat.mod_self, euclidSteps_zero]

/-- Lamé's lower bounds on both operands, for strict ordered positive input. -/
theorem euclid_fibonacci_lower (u v : ℕ) (hv : 0 < v) (hvu : v < u) :
    Nat.fib (euclidSteps u v + 2) ≤ u ∧ Nat.fib (euclidSteps u v + 1) ≤ v := by
  rw [euclidSteps, dite_eq_right (ne_of_gt hv)]
  by_cases hr : u % v = 0
  · rw [hr, euclidSteps_zero]
    norm_num
    omega
  · have hrv := Nat.mod_lt u hv
    obtain ⟨h1, h2⟩ := euclid_fibonacci_lower v (u % v) (Nat.pos_of_ne_zero hr) hrv
    have hq : 1 ≤ u / v := (Nat.le_div_iff_mul_le hv).2 (by omega)
    have heq := Nat.mod_add_div u v
    have hsum : v + u % v ≤ u := by nlinarith
    constructor
    · rw [show euclidSteps v (u % v) + 1 + 2 =
        (euclidSteps v (u % v) + 1) + 2 by omega, Nat.fib_add_two]
      change Nat.fib (euclidSteps v (u % v) + 1) +
        Nat.fib (euclidSteps v (u % v) + 2) ≤ u
      omega
    · simpa only [Nat.add_assoc] using h1
termination_by v
decreasing_by exact Nat.mod_lt _ hv

private theorem fib_strict_successor (n : ℕ) : Nat.fib (n + 2) < Nat.fib (n + 3) := by
  have hp : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have he : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) :=
    Nat.fib_add_two
  omega

/-- Every positive division count is attained by consecutive Fibonacci inputs. -/
theorem euclid_fibonacci_steps (n : ℕ) :
    euclidSteps (Nat.fib (n + 3)) (Nat.fib (n + 2)) = n + 1 := by
  induction n with
  | zero => norm_num [Nat.fib, euclidSteps]
  | succ n ih =>
    have hp : 0 < Nat.fib (n + 3) := Nat.fib_pos.mpr (by omega)
    have hm : Nat.fib (n + 4) % Nat.fib (n + 3) = Nat.fib (n + 2) := by
      have he : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) :=
        Nat.fib_add_two
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (fib_strict_successor n)]
    change euclidSteps (Nat.fib (n + 4)) (Nat.fib (n + 3)) = n + 2
    rw [euclidSteps, dite_eq_right (ne_of_gt hp), hm, ih]

/-- The exact Fibonacci minimality used for the comparison in §7, including
its necessary boundary condition on the division count. -/
theorem euclid_fibonacci_minimal {n : ℕ} (hn : 2 ≤ n) :
    euclidSteps (Nat.fib (n + 2)) (Nat.fib (n + 1)) = n ∧
      ∀ u v : ℕ, 0 < u → v ≤ u → euclidSteps u v = n →
        LexLE (Nat.fib (n + 2), Nat.fib (n + 1)) (u, v) := by
  constructor
  · have h := euclid_fibonacci_steps (n - 1)
    rw [show n - 1 + 3 = n + 2 by omega, show n - 1 + 2 = n + 1 by omega,
      show n - 1 + 1 = n by omega] at h
    exact h
  · intro u v hu hvu hc
    have hv : 0 < v := by
      by_contra h
      have hz : v = 0 := by omega
      rw [hz, euclidSteps_zero] at hc
      omega
    have hstrict : v < u := by
      by_contra h
      have he : u = v := by omega
      subst u
      rw [euclidSteps_same hv] at hc
      omega
    obtain ⟨h1, h2⟩ := euclid_fibonacci_lower u v hv hstrict
    rw [hc] at h1 h2
    unfold LexLE
    omega

/-- The exceptional least input for one division with non-strict input order. -/
theorem euclid_one_minimal : euclidSteps 1 1 = 1 ∧
    ∀ u v : ℕ, 0 < u → v ≤ u → euclidSteps u v = 1 → LexLE (1, 1) (u, v) := by
  constructor
  · exact euclidSteps_same (by decide)
  · intro u v hu hvu hc
    have hv : 0 < v := by
      by_contra h
      have hz : v = 0 := by omega
      rw [hz, euclidSteps_zero] at hc
      omega
    unfold LexLE
    omega

/-- Fibonacci growth at the exact exponential rate needed by Lamé's bound. -/
theorem fibonacci_exponential_growth (n : ℕ) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · norm_num
    · simpa [Nat.fib] using le_of_lt Real.goldenRatio_lt_two
    · have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have hf : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        exact_mod_cast (Nat.fib_add_two (n := n + 2))
      have hp : Real.goldenRatio ^ (n + 2) =
          Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
        rw [pow_add, Real.goldenRatio_sq, pow_succ]
        ring
      change Real.goldenRatio ^ (n + 2) ≤ (Nat.fib (n + 4) : ℝ)
      rw [hp, hf]
      exact add_le_add h0 h1

/-- The coefficient `1 / log₂ φ` for Euclidean division steps, with an
explicit constant accommodating the equal-input boundary. -/
theorem euclidSteps_le_log {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (euclidSteps u v : ℝ) ≤ Real.log u / Real.log Real.goldenRatio + 1 := by
  have hphi := Real.one_lt_goldenRatio
  have hlog := Real.log_pos hphi
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hul : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  by_cases hv : v = 0
  · rw [hv, euclidSteps_zero]
    simp only [Nat.cast_zero]
    positivity
  by_cases he : u = v
  · subst v
    rw [euclidSteps_same hu]
    have hq : 0 ≤ Real.log u / Real.log Real.goldenRatio := by positivity
    norm_num only [Nat.cast_one]
    linarith
  have hstrict : v < u := by omega
  have h1 := (euclid_fibonacci_lower u v (Nat.pos_of_ne_zero hv) hstrict).1
  have hg : Real.goldenRatio ^ euclidSteps u v ≤ (u : ℝ) :=
    (fibonacci_exponential_growth _).trans (by exact_mod_cast h1)
  have hl := Real.log_le_log (by positivity : 0 < Real.goldenRatio ^ euclidSteps u v) hg
  rw [Real.log_pow] at hl
  have hb := (le_div_iff₀ hlog).2 hl
  linarith

/-- The Euclidean bound written with the paper's binary logarithm coefficient. -/
theorem euclidSteps_le_log2 {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (euclidSteps u v : ℝ) ≤
      1 / Real.logb 2 Real.goldenRatio * Real.logb 2 u + 1 := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hp : Real.log Real.goldenRatio ≠ 0 :=
    ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  have he : 1 / Real.logb 2 Real.goldenRatio * Real.logb 2 u =
      Real.log u / Real.log Real.goldenRatio := by
    unfold Real.logb
    field_simp
  rw [he]
  exact euclidSteps_le_log hu hvu

/-- Ratio of the two worst-case leading iteration coefficients in §7. -/
noncomputable def iterationCoefficientRatio : ℝ :=
  (1 / Real.logb 2 (Real.sqrt alpha)) / (1 / Real.logb 2 Real.goldenRatio)

theorem iterationCoefficientRatio_eq :
    iterationCoefficientRatio = 2 * Real.log Real.goldenRatio / Real.log alpha := by
  have ha : 0 < alpha := by linarith [characteristic_root_bounds.1]
  have hal : Real.log alpha ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith [characteristic_root_bounds.1]))
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hp : Real.log Real.goldenRatio ≠ 0 :=
    ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  unfold iterationCoefficientRatio Real.logb
  rw [Real.log_sqrt (le_of_lt ha)]
  field_simp

private theorem characteristic_rational_bounds :
    (3732 / 1000 : ℝ) ≤ alpha ∧ alpha ≤ 3733 / 1000 ∧
      (1618 / 1000 : ℝ) ≤ Real.goldenRatio ∧ Real.goldenRatio ≤ 1619 / 1000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hp := Real.goldenRatio_sq
  have hp0 := Real.one_lt_goldenRatio
  dsimp [alpha]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Rigorous rational enclosure of the ratio, justifying the paper's
approximately 27% reduction in the worst-case leading iteration coefficient.
The only numerical calculations here are exact rational powers. -/
theorem iterationCoefficientRatio_bounds :
    (730 / 1000 : ℝ) < iterationCoefficientRatio ∧
      iterationCoefficientRatio < 732 / 1000 := by
  obtain ⟨hal, hau, hpl, hpu⟩ := characteristic_rational_bounds
  have ha0 : 0 < alpha := by linarith
  have hp0 := Real.goldenRatio_pos
  have hlo : alpha ^ 73 < Real.goldenRatio ^ 200 := by
    calc
      alpha ^ 73 ≤ (3733 / 1000 : ℝ) ^ 73 := pow_le_pow_left₀ (le_of_lt ha0) hau _
      _ < (1618 / 1000 : ℝ) ^ 200 := by norm_num
      _ ≤ Real.goldenRatio ^ 200 := pow_le_pow_left₀ (by norm_num) hpl _
  have hhi : Real.goldenRatio ^ 500 < alpha ^ 183 := by
    calc
      Real.goldenRatio ^ 500 ≤ (1619 / 1000 : ℝ) ^ 500 :=
        pow_le_pow_left₀ (le_of_lt hp0) hpu _
      _ < (3732 / 1000 : ℝ) ^ 183 := by
        set_option exponentiation.threshold 500 in norm_num
      _ ≤ alpha ^ 183 := pow_le_pow_left₀ (by norm_num) hal _
  have hll := Real.log_lt_log (by positivity : 0 < alpha ^ 73) hlo
  have hhl := Real.log_lt_log (by positivity : 0 < Real.goldenRatio ^ 500) hhi
  rw [Real.log_pow, Real.log_pow] at hll hhl
  have hlog : 0 < Real.log alpha :=
    Real.log_pos (by linarith [characteristic_root_bounds.1])
  rw [iterationCoefficientRatio_eq]
  constructor
  · apply (lt_div_iff₀ hlog).2
    norm_num only [Nat.cast_ofNat] at hll
    linarith
  · apply (div_lt_iff₀ hlog).2
    norm_num only [Nat.cast_ofNat] at hhl
    linarith

/-- The leading-coefficient saving lies strictly between 26.8% and 27%. -/
theorem iterationCoefficientSaving_bounds :
    (268 / 1000 : ℝ) < 1 - iterationCoefficientRatio ∧
      1 - iterationCoefficientRatio < 270 / 1000 := by
  obtain ⟨hlo, hhi⟩ := iterationCoefficientRatio_bounds
  constructor <;> linarith

/-- The Fibonacci asymptotic quoted in §7, as an exact ratio limit. -/
theorem fibonacci_asymptotic : Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) /
    (Real.goldenRatio ^ (n + 2) / Real.sqrt 5)) atTop (nhds 1) := by
  have hr : abs (Real.goldenConj / Real.goldenRatio) < 1 := by
    rw [abs_div, abs_of_pos Real.goldenRatio_pos,
      div_lt_one Real.goldenRatio_pos, abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj, Real.one_lt_goldenRatio]
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hp' : Tendsto (fun n : ℕ => (Real.goldenConj / Real.goldenRatio) ^ (n + 2))
      atTop (nhds 0) := by
    simpa only [pow_add, zero_mul] using hp.mul_const ((Real.goldenConj / Real.goldenRatio) ^ 2)
  have he (n : ℕ) : (Nat.fib (n + 2) : ℝ) /
      (Real.goldenRatio ^ (n + 2) / Real.sqrt 5) =
        1 - (Real.goldenConj / Real.goldenRatio) ^ (n + 2) := by
    have hid (a b c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (k : ℕ) :
        ((a ^ k - b ^ k) / c) / (a ^ k / c) = 1 - (b / a) ^ k := by
      rw [div_pow]
      field_simp
    rw [Real.coe_fib_eq]
    exact hid _ _ _ Real.goldenRatio_ne_zero (by positivity) _
  simp_rw [he]
  have h := Filter.Tendsto.const_sub 1 hp'
  simpa using h

end Lsbgcd
