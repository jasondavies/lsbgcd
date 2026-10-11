import Lsbgcd.Complexity
import Lsbgcd.ClosedForms
import Lsbgcd.Minimality

/-!
# The sharp logarithmic coefficient

The closed forms give an unconditional exponential lower bound for the
constructed candidates. The proved global minimality theorem then gives the coefficient
`1 / log₂ √(2 + √3)` stated in §7. The explicit additive constant below
replaces the paper's `O(1)` term.
-/
namespace Lsbgcd

private theorem sqrt_three_bounds : 1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hnonneg := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

/-- Useful real-root bounds for the two characteristic roots. -/
theorem characteristic_root_bounds : 3 ≤ alpha ∧ 0 ≤ beta ∧ beta ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := sqrt_three_bounds
  unfold alpha beta
  constructor
  · linarith
  constructor <;> linarith

private theorem candidate_odd_growth (k : ℕ) :
    alpha ^ k ≤ 3 * ((candidate (2 * k + 1)).1 : ℝ) := by
  obtain ⟨ha, hb0, hb1⟩ := characteristic_root_bounds
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp : 1 ≤ alpha ^ k := one_le_pow₀ (by linarith)
  have hbp : beta ^ (k + 1) ≤ 1 := pow_le_one₀ hb0 hb1
  have hd : 2 * alpha ^ k ≤ alpha ^ k * alpha - beta ^ (k + 1) := by
    nlinarith
  have hm : 2 * alpha ^ k ≤
      Real.sqrt 3 * (alpha ^ k * alpha - beta ^ (k + 1)) := by
    have hp' : 0 ≤ alpha ^ k * alpha - beta ^ (k + 1) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hp']
  rw [candidate_odd_x_closed, pow_succ]
  nlinarith

private theorem candidate_even_growth (k : ℕ) :
    alpha ^ (2 * k) ≤ 3 * ((candidate (4 * k)).1 : ℝ) := by
  obtain ⟨ha, hb0, hb1⟩ := characteristic_root_bounds
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp : 0 ≤ alpha ^ (2 * k) := by positivity
  have hp' : 3 * alpha ^ (2 * k) ≤ alpha ^ (2 * k + 1) := by
    rw [pow_succ]
    nlinarith
  have hm : 2 * alpha ^ (2 * k + 1) ≤
      (4 - Real.sqrt 3) * alpha ^ (2 * k + 1) := by
    have : 0 ≤ alpha ^ (2 * k + 1) := by positivity
    nlinarith
  have hb : 0 ≤ (4 + Real.sqrt 3) * beta ^ (2 * k + 1) := by positivity
  rw [candidate_even_x_closed]
  nlinarith

private theorem candidate_offset_growth (k : ℕ) :
    alpha ^ (2 * k + 1) ≤ 3 * ((candidate (4 * k + 2)).1 : ℝ) := by
  obtain ⟨ha, hb0, hb1⟩ := characteristic_root_bounds
  obtain ⟨hs1, hs2⟩ := sqrt_three_bounds
  have hp : 0 ≤ alpha ^ (2 * k + 1) := by positivity
  have hp' : 3 * alpha ^ (2 * k + 1) ≤ alpha ^ (2 * k + 2) := by
    calc
      3 * alpha ^ (2 * k + 1) ≤ alpha ^ (2 * k + 1) * alpha := by nlinarith
      _ = alpha ^ (2 * k + 2) := (pow_succ alpha (2 * k + 1)).symm
  have hm : 2 * alpha ^ (2 * k + 2) ≤
      (4 - Real.sqrt 3) * alpha ^ (2 * k + 2) := by
    have : 0 ≤ alpha ^ (2 * k + 2) := by positivity
    nlinarith
  have hb : 0 ≤ (4 + Real.sqrt 3) * beta ^ (2 * k + 2) := by positivity
  rw [candidate_offset_x_closed]
  nlinarith

/-- Candidate numerators grow at least as fast as powers of `√alpha`,
with an explicit uniform constant. -/
theorem candidate_exponential_growth (n : ℕ) :
    alpha ^ (n / 2) ≤ 3 * ((candidate n).1 : ℝ) := by
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with h | h | h | h
  · have hn : n = 4 * (n / 4) := by omega
    have hd : n / 2 = 2 * (n / 4) := by omega
    rw [hd]
    conv_rhs => rw [hn]
    exact candidate_even_growth (n / 4)
  · have hn : n = 2 * (n / 2) + 1 := by omega
    conv_rhs => rw [hn]
    exact candidate_odd_growth (n / 2)
  · have hn : n = 4 * (n / 4) + 2 := by omega
    have hd : n / 2 = 2 * (n / 4) + 1 := by omega
    rw [hd]
    conv_rhs => rw [hn]
    exact candidate_offset_growth (n / 4)
  · have hn : n = 2 * (n / 2) + 1 := by omega
    conv_rhs => rw [hn]
    exact candidate_odd_growth (n / 2)

/-- The sharp logarithmic iteration estimate, conditional precisely on global
minimality. It applies to zero smaller operands as well. -/
theorem iterations_le_sharp_log_of_minimality (minimality : CandidateMinimality)
    {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ 2 / Real.log alpha * Real.log u +
      (2 * Real.log 3 / Real.log alpha + 1) := by
  let n := iterations u v
  have hmin := (minimality n).2.2.2 u v hu hvu rfl
  have hx : (candidate n).1 ≤ u := by
    unfold LexLE at hmin
    omega
  have hg : alpha ^ (n / 2) ≤ 3 * (u : ℝ) := by
    have hxr : ((candidate n).1 : ℝ) ≤ u := by exact_mod_cast hx
    exact (candidate_exponential_growth n).trans (by linarith)
  have ha : 1 < alpha := by linarith [characteristic_root_bounds.1]
  have hlog : 0 < Real.log alpha := Real.log_pos ha
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hl := Real.log_le_log (by positivity : 0 < alpha ^ (n / 2)) hg
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hur)] at hl
  have hn : n ≤ 2 * (n / 2) + 1 := by omega
  have hnr : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast hn
  change (n : ℝ) ≤ _
  apply (le_div_iff₀ hlog).2 at hl
  calc
    (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := hnr
    _ ≤ 2 * ((Real.log 3 + Real.log u) / Real.log alpha) + 1 := by linarith
    _ = _ := by ring

/-- The natural-log coefficient in the preceding bound is exactly the
base-two coefficient stated in §7 of the paper. -/
theorem sharp_log_coefficient :
    1 / Real.logb 2 (Real.sqrt alpha) / Real.log 2 = 2 / Real.log alpha := by
  have ha : 0 < alpha := by linarith [characteristic_root_bounds.1]
  rw [Real.logb, Real.log_sqrt (le_of_lt ha)]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hal : Real.log alpha ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith [characteristic_root_bounds.1]))
  field_simp

/-- The sharp estimate from §7, now using the unconditional minimality theorem. -/
theorem iterations_le_sharp_log {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ 2 / Real.log alpha * Real.log u +
      (2 * Real.log 3 / Real.log alpha + 1) :=
  iterations_le_sharp_log_of_minimality candidate_minimality hu hvu

/-- The paper's base-two form, with an explicit additive constant. -/
theorem iterations_le_sharp_log2 {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤
      1 / Real.logb 2 (Real.sqrt alpha) * Real.logb 2 u +
        (2 * Real.log 3 / Real.log alpha + 1) := by
  have hcoeff : 1 / Real.logb 2 (Real.sqrt alpha) * Real.logb 2 u =
      2 / Real.log alpha * Real.log u := by
    calc
      _ = (1 / Real.logb 2 (Real.sqrt alpha) / Real.log 2) * Real.log u := by
        change (1 / Real.logb 2 (Real.sqrt alpha)) * (Real.log u / Real.log 2) = _
        ring
      _ = _ := by rw [sharp_log_coefficient]
  rw [hcoeff]
  exact iterations_le_sharp_log hu hvu

end Lsbgcd
