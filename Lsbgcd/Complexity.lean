import Lsbgcd.Algorithm

/-!
# Unconditional iteration bounds

The product of the two live operands contracts by at least a factor of three
at every iteration. This gives the logarithmic iteration bound stated on
p. 474 independently of the exact extremal analysis in Theorem 1.1.
-/
namespace Lsbgcd

/-- The nearest of the two adjacent shifted multiples is at distance at most
one third of the original larger operand. -/
theorem remainder_triple_le {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    3 * remainder u v ≤ u := by
  obtain ⟨hlo, hhi⟩ := shift_bounds hv hvu
  have hp : 2 ^ (shift u v + 1) * v = 2 * (2 ^ shift u v * v) := by
    rw [pow_succ]
    ring
  have hleft : remainder u v ≤ u - 2 ^ shift u v * v := min_le_left _ _
  have hright : remainder u v ≤ 2 ^ (shift u v + 1) * v - u := min_le_right _ _
  rw [hp] at hhi hright
  omega

/-- Sorting does not change the product of the next two operands. -/
theorem step_product (u v : ℕ) :
    (step u v).1 * (step u v).2 = v * remainder u v := by
  unfold step
  rcases le_total v (remainder u v) with h | h
  · simp [max_eq_right h, min_eq_left h, Nat.mul_comm]
  · simp [max_eq_left h, min_eq_right h]

/-- The live-operand product decreases by a factor of at least three. -/
theorem step_product_contracts {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    3 * ((step u v).1 * (step u v).2) ≤ u * v := by
  rw [step_product]
  have h := Nat.mul_le_mul_right v (remainder_triple_le hv hvu)
  nlinarith

/-- Exponential lower bound on the input product in terms of its exact
iteration count. The factor three accounts for the last, zeroing step. -/
theorem run_power_bound (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) :
    3 ^ (run u v hvu).2 ≤ 3 * (u * v) := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  rw [run, dite_eq_right (by omega : v ≠ 0)]
  dsimp only
  by_cases hn : (step u v).2 = 0
  · have hr : run (step u v).1 (step u v).2 (step_ordered u v) =
        ((step u v).1, 0) := by rw [run, dite_eq_left hn]
    rw [hr]
    dsimp only
    have huv : 1 ≤ u * v := Nat.one_le_iff_ne_zero.mpr (by positivity)
    norm_num only [pow_one]
    omega
  · have ih := run_power_bound (step u v).1 (step u v).2
        (Nat.pos_of_ne_zero hn) (step_ordered u v)
    rw [pow_succ]
    have hc := step_product_contracts hv hvu
    nlinarith
termination_by u + v
decreasing_by exact step_decreases hv hvu

/-- The algorithm uses at most `1 + ⌊log₃(uv)⌋` iterations on positive,
ordered input. In particular its iteration count is logarithmic. -/
theorem iterations_le_log_product {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    iterations u v ≤ Nat.log 3 (u * v) + 1 := by
  rw [iterations_of_ordered hvu]
  have h := Nat.le_log_of_pow_le (by decide : 1 < 3) (run_power_bound u v hv hvu)
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have huv : u * v ≠ 0 := by positivity
  simpa only [Nat.mul_comm 3, Nat.log_mul_base (by decide : 1 < 3) huv] using h

end Lsbgcd
