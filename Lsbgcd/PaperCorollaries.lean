module

public import Lsbgcd.Minimality
public import Lsbgcd.Computation
public import Lsbgcd.Examples
public import Lsbgcd.EuclideanComparison
public import Lsbgcd.ContinuantOrder

@[expose] public section

/-!
# Further statements from the paper

This module supplies the rational interpretation of continued fractions in
§5, the assertion in §§1 and 4 that worst-case computations use only A₀
and A₁, and the introductory observation that the worst-case fractions
are not the successive truncations of a single continued fraction.
-/
namespace Lsbgcd

/-- Equation (5.1), evaluated over the rationals. The empty list is assigned
zero, so the same recursive clause also handles a singleton. -/
def continuedFraction : List ℕ → ℚ
  | [] => 0
  | a :: as => a + 1 / continuedFraction as

/-- The numerator and denominator in §5 really evaluate the fraction (5.1). -/
theorem continuedFraction_eq_convergent {as : List ℕ} (h : ∀ a ∈ as, 0 < a) :
    continuedFraction as = (convergent as).1 / (convergent as).2 := by
  induction as with
  | nil => simp [continuedFraction, convergent]
  | cons a as ih =>
    have ht : ∀ b ∈ as, 0 < b := fun b hb => h b (by simp [hb])
    have hx : ((convergent as).1 : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (positive_convergent ht).1
    simp only [continuedFraction, convergent, ih ht, Nat.cast_add, Nat.cast_mul,
      one_div_div]
    field_simp

/-- Admissible words have positive digits, so (5.1) evaluates their convergents. -/
theorem admissible_continuedFraction {as : List ℕ} (h : Admissible as) :
    continuedFraction as = (convergent as).1 / (convergent as).2 := by
  apply continuedFraction_eq_convergent
  intro a ha
  have := admissible_digits h a ha
  omega

/-- Inverse execution order for the Euclidean A-steps represented by a word. -/
def wordComputation (as : List ℕ) : List Transformation :=
  as.reverse.map (fun a => .A (a - 1))

/-- Each admissible word is the valid inverse computation of its convergent from
the terminal pair `(1, 0)`. -/
theorem wordComputation_valid {as : List ℕ} (h : Admissible as) :
    ValidComputation (wordComputation as) (1, 0) ∧
      inverseComputation (wordComputation as) (1, 0) = convergent as := by
  induction as with
  | nil => exact ⟨trivial, rfl⟩
  | cons a as ih =>
    have ht := admissible_tail h
    obtain ⟨hv, hi⟩ := ih ht
    obtain ⟨hx, hxy⟩ := admissible_convergent ht
    have hw : wordComputation (a :: as) = wordComputation as ++ [.A (a - 1)] := by
      simp [wordComputation]
    rw [hw, validComputation_append, inverseComputation_append, hi]
    refine ⟨⟨hv, ?_⟩, ?_⟩
    · refine ⟨?_, trivial⟩
      rcases admissible_head h with rfl | rfl
      · apply (Transformation.validA_iff _ _ _).2
        exact ⟨hx, hxy, by simpa using admissible_one_bound h⟩
      · apply (Transformation.validA_iff _ _ _).2
        exact ⟨hx, hxy, by simpa using Nat.mul_le_mul_left 2 hxy⟩
    · rcases admissible_head h with rfl | rfl <;>
        simp [inverseComputation, Transformation.inverse, inverseA, convergent]

/-- The prose assertion in §§1 and 4: the worst-case computation has only
A₀ and A₁ steps, so it never chooses B or performs an interchange. -/
theorem worst_case_computation {n : ℕ} {p : ℕ × ℕ} (h : IsWorstCase n p) :
    ∃ ss : List Transformation, ss.length = n ∧
      (∀ s ∈ ss, s = .A 0 ∨ s = .A 1) ∧
      ValidComputation ss (1, 0) ∧ inverseComputation ss (1, 0) = p := by
  have hp := (isWorstCase_iff n p).1 h
  subst p
  obtain ⟨hv, hi⟩ := wordComputation_valid (candidateWord_admissible n)
  refine ⟨wordComputation (candidateWord n), ?_, ?_, hv, hi⟩
  · simp [wordComputation, candidateWord_length]
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
    have hd := admissible_digits (candidateWord_admissible n) a (List.mem_reverse.1 ha)
    rcases hd with rfl | rfl <;> simp

/-- The paper's finite list of worst-case partial quotients cannot be the
successive truncations of one infinite list of positive partial quotients.
The first two worst-case ratios already force incompatible truncations. -/
theorem worst_cases_not_one_continued_fraction :
    ¬ ∃ digits : ℕ → ℕ, (∀ i, 0 < digits i) ∧
      ∀ n, 0 < n → continuedFraction ((List.range n).map digits) =
        (candidate n).1 / (candidate n).2 := by
  rintro ⟨digits, hpos, h⟩
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  norm_num [List.range_succ, continuedFraction, candidate, candidateWord, blockWord,
    repeat12, repeat21, convergent] at h1 h2
  have hd : (1 : ℚ) ≤ digits 1 := by exact_mod_cast hpos 1
  have hz : (digits 1 : ℚ) ≠ 0 := by linarith
  have he : (1 : ℚ) / digits 1 = 2 := by
    rw [one_div]
    norm_num [h1] at h2
    linarith
  have hm := (div_eq_iff hz).1 he
  linarith

/-- Table 1 now carries its full claimed worst-case interpretation. -/
theorem table1_worst_cases (i : Fin 20) :
    IsWorstCase (i.val + 1) (table1[i.val]'i.isLt) := by
  have he : table1[i.val]'i.isLt = candidate (i.val + 1) := by
    simp [← table1_candidates]
  rw [he]
  exact candidate_minimality _

/-- The decimal coefficient printed for LSBGCD in §7 is a valid upper bound.
The numerical certificate is the exact inequality `2 ^ 302 < alpha ^ 159`,
which gives `1 / log₂ √alpha < 318 / 302 < 1.053`. The margin is narrow,
since `1 / log₂ √alpha ≈ 1.0526`, so the exponents must be large; the
exponentiation threshold is raised just enough to evaluate this power. -/
theorem lsb_iteration_coefficient_lt_decimal :
    1 / Real.logb 2 (Real.sqrt alpha) < (1053 / 1000 : ℝ) := by
  have hal := characteristic_rational_bounds.1
  have hpow : (2 : ℝ) ^ 302 < alpha ^ 159 := by
    calc
      (2 : ℝ) ^ 302 < (373205 / 100000 : ℝ) ^ 159 := by
        set_option exponentiation.threshold 302 in norm_num
      _ ≤ alpha ^ 159 := pow_le_pow_left₀ (by norm_num) hal _
  have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ 302) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog := log_alpha_pos
  rw [one_div_logb_sqrt_alpha]
  apply (div_lt_iff₀ hlog).2
  linarith

/-- The decimal coefficient printed for ordinary Euclid in §7 is likewise
a valid upper bound. The certificate `2 ^ 59 < φ ^ 85` gives
`1 / log₂ φ < 85 / 59 < 1.441`. -/
theorem euclid_iteration_coefficient_lt_decimal :
    1 / Real.logb 2 Real.goldenRatio < (1441 / 1000 : ℝ) := by
  have hpl := characteristic_rational_bounds.2.2.1
  have hpow : (2 : ℝ) ^ 59 < Real.goldenRatio ^ 85 := by
    calc
      (2 : ℝ) ^ 59 < (161803 / 100000 : ℝ) ^ 85 := by norm_num
      _ ≤ Real.goldenRatio ^ 85 := pow_le_pow_left₀ (by norm_num) hpl _
  have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ 59) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hpLog : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  rw [one_div_logb_goldenRatio]
  apply (div_lt_iff₀ hpLog).2
  linarith

/-- The paper's `1.053 log₂ u + O(1)` estimate, with the additive constant
made explicit and its printed decimal justified. -/
theorem iterations_le_decimal_logb {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ (1053 / 1000 : ℝ) * Real.logb 2 u +
      (2 * Real.log 3 / Real.log alpha + 1) := by
  have hlu2 : 0 ≤ Real.logb 2 u := Real.logb_nonneg one_lt_two (by exact_mod_cast hu)
  exact (iterations_le_sharp_logb hu hvu).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (le_of_lt lsb_iteration_coefficient_lt_decimal) hlu2) le_rfl)

/-- The corresponding `1.441 log₂ u + O(1)` Euclidean estimate. -/
theorem euclidSteps_le_decimal_logb {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (euclidSteps u v : ℝ) ≤ (1441 / 1000 : ℝ) * Real.logb 2 u + 1 := by
  have hlu2 : 0 ≤ Real.logb 2 u := Real.logb_nonneg one_lt_two (by exact_mod_cast hu)
  exact (euclidSteps_le_logb hu hvu).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (le_of_lt euclid_iteration_coefficient_lt_decimal) hlu2) le_rfl)

end Lsbgcd
