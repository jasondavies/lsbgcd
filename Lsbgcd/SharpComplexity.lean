module

public import Lsbgcd.Complexity
public import Lsbgcd.ClosedForms
public import Lsbgcd.Minimality

@[expose] public section

/-!
# The sharp logarithmic coefficient

The closed forms give an unconditional exponential lower bound for the
constructed candidates. The proved global minimality theorem then gives the coefficient
`1 / log₂ √(2 + √3)` stated in §7. The explicit additive constant below
replaces the paper's `O(1)` term.
-/
namespace Lsbgcd

/-- Coarse bounds on `√3`, sufficient for the growth estimates below. -/
theorem sqrt_three_bounds : 1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
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

theorem alpha_pos : 0 < alpha := by linarith [characteristic_root_bounds.1]

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

theorem log_alpha_pos : 0 < Real.log alpha :=
  Real.log_pos (by linarith [characteristic_root_bounds.1])

/-- Each further power of `alpha` gains at least a factor of three. -/
private theorem three_mul_alpha_pow_le (m : ℕ) : 3 * alpha ^ m ≤ alpha ^ (m + 1) := by
  have h := mul_le_mul_of_nonneg_left characteristic_root_bounds.1
    (pow_nonneg alpha_pos.le m)
  rw [pow_succ]
  linarith

private theorem candidate_odd_growth (k : ℕ) :
    alpha ^ k ≤ 3 * ((candidate (2 * k + 1)).1 : ℝ) := by
  obtain ⟨ha, hb0, hb1⟩ := characteristic_root_bounds
  have hp : 1 ≤ alpha ^ k := one_le_pow₀ (by linarith)
  have hb : beta ^ (k + 1) ≤ 1 := pow_le_one₀ hb0 hb1
  have hstep := three_mul_alpha_pow_le k
  have hd : 0 ≤ alpha ^ (k + 1) - beta ^ (k + 1) := by linarith
  have hm := mul_le_mul_of_nonneg_right sqrt_three_bounds.1 hd
  rw [candidate_odd_x_closed]
  linarith

/-- The common estimate for the two even closed forms of Theorem 1.1, whose
constant terms `c` are `2` and `4`. -/
private theorem even_closed_form_growth (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    alpha ^ m ≤ 3 * ((c + (4 - Real.sqrt 3) * alpha ^ (m + 1) +
      (4 + Real.sqrt 3) * beta ^ (m + 1)) / 12) := by
  have hp := pow_nonneg alpha_pos.le m
  have hstep := three_mul_alpha_pow_le m
  have hcoeff : 2 * alpha ^ (m + 1) ≤ (4 - Real.sqrt 3) * alpha ^ (m + 1) :=
    mul_le_mul_of_nonneg_right (by linarith [sqrt_three_bounds.2])
      (pow_nonneg alpha_pos.le _)
  have hb : 0 ≤ (4 + Real.sqrt 3) * beta ^ (m + 1) :=
    mul_nonneg (by positivity) (pow_nonneg characteristic_root_bounds.2.1 _)
  linarith

private theorem candidate_even_growth (k : ℕ) :
    alpha ^ (2 * k) ≤ 3 * ((candidate (4 * k)).1 : ℝ) := by
  rw [candidate_even_x_closed]
  exact even_closed_form_growth (2 * k) (by norm_num)

private theorem candidate_offset_growth (k : ℕ) :
    alpha ^ (2 * k + 1) ≤ 3 * ((candidate (4 * k + 2)).1 : ℝ) := by
  rw [candidate_offset_x_closed]
  exact even_closed_form_growth (2 * k + 1) (by norm_num)

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
  have hlog := log_alpha_pos
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hl := Real.log_le_log (pow_pos alpha_pos _) hg
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hur)] at hl
  have hn : n ≤ 2 * (n / 2) + 1 := by omega
  have hnr : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast hn
  change (n : ℝ) ≤ _
  apply (le_div_iff₀ hlog).2 at hl
  calc
    (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := hnr
    _ ≤ 2 * ((Real.log 3 + Real.log u) / Real.log alpha) + 1 := by linarith
    _ = _ := by ring

/-- The paper's base-two coefficient `1 / log₂ √alpha`, in natural logarithms. -/
theorem one_div_logb_sqrt_alpha :
    1 / Real.logb 2 (Real.sqrt alpha) = 2 * Real.log 2 / Real.log alpha := by
  rw [Real.logb, Real.log_sqrt alpha_pos.le]
  have hal := log_alpha_pos.ne'
  field_simp

/-- The natural-log coefficient in the preceding bound is exactly the
base-two coefficient stated in §7 of the paper. -/
theorem sharp_log_coefficient :
    1 / Real.logb 2 (Real.sqrt alpha) / Real.log 2 = 2 / Real.log alpha := by
  rw [one_div_logb_sqrt_alpha]
  have h2 := log_two_pos.ne'
  field_simp

/-- The sharp estimate from §7, now using the unconditional minimality theorem. -/
theorem iterations_le_sharp_log {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ 2 / Real.log alpha * Real.log u +
      (2 * Real.log 3 / Real.log alpha + 1) :=
  iterations_le_sharp_log_of_minimality candidate_minimality hu hvu

/-- The paper's base-two form, with an explicit additive constant. -/
theorem iterations_le_sharp_logb {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
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
