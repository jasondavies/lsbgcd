module

public import Lsbgcd.MainRecurrence

@[expose] public section

/-! # Closed forms for the candidate sequences (Theorem 1.1) -/
namespace Lsbgcd

private theorem alpha_quadratic : alpha ^ 2 - 4 * alpha + 1 = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold alpha
  nlinarith

private theorem beta_quadratic : beta ^ 2 - 4 * beta + 1 = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold beta
  nlinarith

private theorem even_root (t : ℝ) (h : t ^ 2 - 4 * t + 1 = 0) :
    t ^ 6 - 15 * t ^ 4 + 15 * t ^ 2 - 1 = 0 := by
  linear_combination (t ^ 4 + 4 * t ^ 3 - 4 * t - 1) * h

private theorem geometric_odd (a b : ℝ) (d n : ℕ) :
    (a * alpha ^ (n + 2 + d) + b * beta ^ (n + 2 + d)) +
      (a * alpha ^ (n + d) + b * beta ^ (n + d)) =
    4 * (a * alpha ^ (n + 1 + d) + b * beta ^ (n + 1 + d)) := by
  simp only [pow_add]
  linear_combination (a * alpha ^ n * alpha ^ d) * alpha_quadratic +
    (b * beta ^ n * beta ^ d) * beta_quadratic

private theorem geometric_even (c a b : ℝ) (d n : ℕ) :
    (c + a * alpha ^ (2 * (n + 3) + d) + b * beta ^ (2 * (n + 3) + d)) +
      15 * (c + a * alpha ^ (2 * (n + 1) + d) + b * beta ^ (2 * (n + 1) + d)) =
    15 * (c + a * alpha ^ (2 * (n + 2) + d) + b * beta ^ (2 * (n + 2) + d)) +
      (c + a * alpha ^ (2 * n + d) + b * beta ^ (2 * n + d)) := by
  simp only [Nat.mul_add, pow_add]
  norm_num only at *
  linear_combination (a * alpha ^ (2 * n) * alpha ^ d) * (even_root alpha alpha_quadratic) +
    (b * beta ^ (2 * n) * beta ^ d) * (even_root beta beta_quadratic)

private theorem sequence2_unique (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ n, f (n + 2) + f n = 4 * f (n + 1))
    (hg : ∀ n, g (n + 2) + g n = 4 * g (n + 1)) (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · exact h0
    · exact h1
    · have h0' := ih n (by omega)
      have h1' := ih (n + 1) (by omega)
      linarith [hf n, hg n]

private theorem sequence3_unique (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2)
    (hf : ∀ n, f (n + 3) + 15 * f (n + 1) = 15 * f (n + 2) + f n)
    (hg : ∀ n, g (n + 3) + 15 * g (n + 1) = 15 * g (n + 2) + g n)
    (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | (_ | n))
    · exact h0
    · exact h1
    · exact h2
    · have h0' := ih n (by omega)
      have h1' := ih (n + 1) (by omega)
      have h2' := ih (n + 2) (by omega)
      linarith [hf n, hg n]

private theorem sqrt3_powers :
    (Real.sqrt 3) ^ 2 = 3 ∧ (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 ∧
    (Real.sqrt 3) ^ 4 = 9 ∧ (Real.sqrt 3) ^ 5 = 9 * Real.sqrt 3 ∧
    (Real.sqrt 3) ^ 6 = 27 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc _ = Real.sqrt 3 * (Real.sqrt 3) ^ 2 := by ring
         _ = _ := by rw [h2]; ring
  have h4 : (Real.sqrt 3) ^ 4 = 9 := by
    calc _ = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
         _ = _ := by rw [h2]; norm_num
  have h5 : (Real.sqrt 3) ^ 5 = 9 * Real.sqrt 3 := by
    calc _ = Real.sqrt 3 * (Real.sqrt 3) ^ 4 := by ring
         _ = _ := by rw [h4]; ring
  have h6 : (Real.sqrt 3) ^ 6 = 27 := by
    calc _ = ((Real.sqrt 3) ^ 2) ^ 3 := by ring
         _ = _ := by rw [h2]; norm_num
  exact ⟨h2, h3, h4, h5, h6⟩

/-- Closes an initial-value goal of a closed form: evaluate the candidate word
at a small index, expand the powers of `α` and `β`, and reduce powers of `√3`. -/
local macro "closed_form_initial" : tactic => `(tactic| (
  obtain ⟨h2, h3, h4, h5, h6⟩ := sqrt3_powers
  norm_num [candidate, candidateWord, blockWord, repeat12, repeat21, convergent, alpha, beta]
  ring_nf
  try norm_num [h2, h3, h4, h5, h6]))

/-- Theorem 1.1's odd x formula, for the constructed candidates. -/
theorem candidate_odd_x_closed (n : ℕ) :
    ((candidate (2 * n + 1)).1 : ℝ) =
      Real.sqrt 3 / 6 * (alpha ^ (n + 1) - beta ^ (n + 1)) := by
  refine sequence2_unique (fun k => ((candidate (2 * k + 1)).1 : ℝ))
    (fun k => Real.sqrt 3 / 6 * (alpha ^ (k + 1) - beta ^ (k + 1))) ?_ ?_
    (fun k => by exact_mod_cast (candidate_odd_recurrence k).1)
    (fun k => by
      convert geometric_odd (Real.sqrt 3 / 6) (-Real.sqrt 3 / 6) 1 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- Theorem 1.1's odd y formula, for the constructed candidates. -/
theorem candidate_odd_y_closed (n : ℕ) :
    ((candidate (2 * n + 1)).2 : ℝ) =
      Real.sqrt 3 / 6 * ((1 + Real.sqrt 3) * alpha ^ n - (1 - Real.sqrt 3) * beta ^ n) := by
  refine sequence2_unique (fun k => ((candidate (2 * k + 1)).2 : ℝ))
    (fun k => Real.sqrt 3 / 6 *
      ((1 + Real.sqrt 3) * alpha ^ k - (1 - Real.sqrt 3) * beta ^ k)) ?_ ?_
    (fun k => by exact_mod_cast (candidate_odd_recurrence k).2)
    (fun k => by
      convert geometric_odd (Real.sqrt 3 / 6 * (1 + Real.sqrt 3))
        (-Real.sqrt 3 / 6 * (1 - Real.sqrt 3)) 0 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- Theorem 1.1's even x formula, for the constructed candidates. -/
theorem candidate_even_x_closed (n : ℕ) :
    ((candidate (4 * n)).1 : ℝ) =
      (2 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 1) +
        (4 + Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 := by
  refine sequence3_unique (fun k => ((candidate (4 * k)).1 : ℝ))
    (fun k => (2 + (4 - Real.sqrt 3) * alpha ^ (2 * k + 1) +
      (4 + Real.sqrt 3) * beta ^ (2 * k + 1)) / 12) ?_ ?_ ?_
    (fun k => by exact_mod_cast (candidate_even_recurrence k).1)
    (fun k => by
      convert geometric_even (2 / 12) ((4 - Real.sqrt 3) / 12) ((4 + Real.sqrt 3) / 12)
        1 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- Theorem 1.1's even y formula, for the constructed candidates. -/
theorem candidate_even_y_closed (n : ℕ) :
    ((candidate (4 * n)).2 : ℝ) =
      (-2 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n) +
        (1 - 3 * Real.sqrt 3) * beta ^ (2 * n)) / 12 := by
  refine sequence3_unique (fun k => ((candidate (4 * k)).2 : ℝ))
    (fun k => (-2 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * k) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * k)) / 12) ?_ ?_ ?_
    (fun k => by exact_mod_cast (candidate_even_recurrence k).2)
    (fun k => by
      convert geometric_even (-2 / 12) ((1 + 3 * Real.sqrt 3) / 12)
        ((1 - 3 * Real.sqrt 3) / 12) 0 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- Theorem 1.1's offset x formula, for the constructed candidates. -/
theorem candidate_offset_x_closed (n : ℕ) :
    ((candidate (4 * n + 2)).1 : ℝ) =
      (4 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 2) +
        (4 + Real.sqrt 3) * beta ^ (2 * n + 2)) / 12 := by
  refine sequence3_unique (fun k => ((candidate (4 * k + 2)).1 : ℝ))
    (fun k => (4 + (4 - Real.sqrt 3) * alpha ^ (2 * k + 2) +
      (4 + Real.sqrt 3) * beta ^ (2 * k + 2)) / 12) ?_ ?_ ?_
    (fun k => by exact_mod_cast (candidate_offset_recurrence k).1)
    (fun k => by
      convert geometric_even (4 / 12) ((4 - Real.sqrt 3) / 12) ((4 + Real.sqrt 3) / 12)
        2 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- Theorem 1.1's offset y formula, for the constructed candidates. -/
theorem candidate_offset_y_closed (n : ℕ) :
    ((candidate (4 * n + 2)).2 : ℝ) =
      (-10 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n + 1) +
        (1 - 3 * Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 := by
  refine sequence3_unique (fun k => ((candidate (4 * k + 2)).2 : ℝ))
    (fun k => (-10 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * k + 1) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * k + 1)) / 12) ?_ ?_ ?_
    (fun k => by exact_mod_cast (candidate_offset_recurrence k).2)
    (fun k => by
      convert geometric_even (-10 / 12) ((1 + 3 * Real.sqrt 3) / 12)
        ((1 - 3 * Real.sqrt 3) / 12) 1 k using 1 <;> ring) n
  all_goals closed_form_initial

/-- All six closed forms, without any minimality assumption. -/
theorem candidate_closed_forms : ClosedForms := by
  intro n
  exact ⟨candidate_odd_x_closed n, candidate_odd_y_closed n,
    candidate_even_x_closed n, candidate_even_y_closed n,
    candidate_offset_x_closed n, candidate_offset_y_closed n⟩

end Lsbgcd
