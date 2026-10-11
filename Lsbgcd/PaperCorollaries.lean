import Lsbgcd.Minimality
import Lsbgcd.Computation
import Lsbgcd.Examples
import Lsbgcd.EuclideanComparison
import Lsbgcd.ContinuantOrder

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

theorem admissible_digits {as : List ℕ} (h : Admissible as) :
    ∀ a ∈ as, a = 1 ∨ a = 2 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact admissible_head h
    · exact ih (admissible_tail h) b hb

theorem admissible_continuedFraction {as : List ℕ} (h : Admissible as) :
    continuedFraction as = (convergent as).1 / (convergent as).2 := by
  apply continuedFraction_eq_convergent
  intro a ha
  have := admissible_digits h a ha
  omega

theorem inverseComputation_append (ss ts : List Transformation) (p : ℕ × ℕ) :
    inverseComputation (ss ++ ts) p =
      inverseComputation ts (inverseComputation ss p) := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih => exact ih (s.inverse p)

theorem validComputation_append (ss ts : List Transformation) (p : ℕ × ℕ) :
    ValidComputation (ss ++ ts) p ↔
      ValidComputation ss p ∧ ValidComputation ts (inverseComputation ss p) := by
  induction ss generalizing p with
  | nil => simp [ValidComputation, inverseComputation]
  | cons s ss ih => simp [ValidComputation, inverseComputation, ih, and_assoc]

/-- Inverse execution order for the Euclidean A-steps represented by a word. -/
def wordComputation (as : List ℕ) : List Transformation :=
  as.reverse.map (fun a => .A (a - 1))

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
  norm_num [List.range_succ, continuedFraction, candidate, candidateWord,
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
    IsWorstCase (i.val + 1) (table1[i.val]'(by change i.val < 20; exact i.isLt)) := by
  have he : table1[i.val]'(by change i.val < 20; exact i.isLt) = candidate (i.val + 1) := by
    simp [← table1_candidates]
  rw [he]
  exact candidate_minimality _

/-- The decimal coefficient printed for LSBGCD in §7 is a valid upper bound.
The numerical certificate is an exact inequality between rational powers. -/
theorem lsb_iteration_coefficient_lt_decimal :
    1 / Real.logb 2 (Real.sqrt alpha) < (1053 / 1000 : ℝ) := by
  have hal : (3732 / 1000 : ℝ) ≤ alpha := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    dsimp [alpha]
    nlinarith
  have hpow : (2 : ℝ) ^ 2000 < alpha ^ 1053 := by
    calc
      (2 : ℝ) ^ 2000 < (3732 / 1000 : ℝ) ^ 1053 := by
        set_option exponentiation.threshold 2000 in norm_num
      _ ≤ alpha ^ 1053 := pow_le_pow_left₀ (by norm_num) hal _
  have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ 2000) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have ha : 0 < alpha := by linarith
  have haLog : 0 < Real.log alpha := Real.log_pos (by linarith)
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : 1 / Real.logb 2 (Real.sqrt alpha) = 2 * Real.log 2 / Real.log alpha := by
    rw [Real.logb, Real.log_sqrt (le_of_lt ha)]
    field_simp
  rw [he]
  apply (div_lt_iff₀ haLog).2
  linarith

/-- The decimal coefficient printed for ordinary Euclid in §7 is likewise
a valid upper bound, certified using only exact rational powers. -/
theorem euclid_iteration_coefficient_lt_decimal :
    1 / Real.logb 2 Real.goldenRatio < (1441 / 1000 : ℝ) := by
  have hpl : (1618 / 1000 : ℝ) ≤ Real.goldenRatio := by
    have hs := Real.goldenRatio_sq
    have hp := Real.one_lt_goldenRatio
    nlinarith
  have hpow : (2 : ℝ) ^ 1000 < Real.goldenRatio ^ 1441 := by
    calc
      (2 : ℝ) ^ 1000 < (1618 / 1000 : ℝ) ^ 1441 := by
        set_option exponentiation.threshold 1441 in norm_num
      _ ≤ Real.goldenRatio ^ 1441 := pow_le_pow_left₀ (by norm_num) hpl _
  have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ 1000) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hpLog : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : 1 / Real.logb 2 Real.goldenRatio = Real.log 2 / Real.log Real.goldenRatio := by
    rw [Real.logb]
    field_simp
  rw [he]
  apply (div_lt_iff₀ hpLog).2
  linarith

/-- The paper's `1.053 log₂ u + O(1)` estimate, with the additive constant
made explicit and its printed decimal justified. -/
theorem iterations_le_decimal_log2 {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ (1053 / 1000 : ℝ) * Real.logb 2 u +
      (2 * Real.log 3 / Real.log alpha + 1) := by
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu2 : 0 ≤ Real.logb 2 u := by unfold Real.logb; positivity
  exact (iterations_le_sharp_log2 hu hvu).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (le_of_lt lsb_iteration_coefficient_lt_decimal) hlu2) le_rfl)

/-- The corresponding `1.441 log₂ u + O(1)` Euclidean estimate. -/
theorem euclidSteps_le_decimal_log2 {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (euclidSteps u v : ℝ) ≤ (1441 / 1000 : ℝ) * Real.logb 2 u + 1 := by
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu2 : 0 ≤ Real.logb 2 u := by unfold Real.logb; positivity
  exact (euclidSteps_le_log2 hu hvu).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (le_of_lt euclid_iteration_coefficient_lt_decimal) hlu2) le_rfl)

end Lsbgcd
