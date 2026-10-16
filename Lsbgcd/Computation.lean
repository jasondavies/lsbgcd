module

public import Lsbgcd.PartialReduction

@[expose] public section

/-!
# Partial computations and the executable algorithm

Every actual nonterminal step has one of the four transformations in §2,
and a valid partial computation contributes exactly its length to the
iteration count.
-/
namespace Lsbgcd

namespace Transformation

theorem valid_input {s : Transformation} {p : ℕ × ℕ} (h : ValidOn s p) :
    0 < (s.inverse p).2 ∧ (s.inverse p).2 ≤ (s.inverse p).1 := by
  have hpow : ∀ e : ℕ, 1 ≤ 2 ^ e := fun e => Nat.one_le_pow e 2 (by decide)
  cases s with
  | A e =>
    refine ⟨h.1.1, ?_⟩
    have hl := h.1.2.1
    have hm := Nat.mul_le_mul_right (inverseA e p).2 (hpow e)
    change (inverseA e p).2 ≤ (inverseA e p).1
    omega
  | B e =>
    refine ⟨h.1.1, ?_⟩
    have hl := h.1.2.1
    have hm := Nat.mul_le_mul_right (inverseB e p).2 (hpow e)
    change (inverseB e p).2 ≤ (inverseB e p).1
    omega
  | IA e =>
    refine ⟨h.1.1, ?_⟩
    have hl := h.1.2.1
    have hm := Nat.mul_le_mul_right (inverseA e (interchange p)).2 (hpow e)
    change (inverseA e (interchange p)).2 ≤ (inverseA e (interchange p)).1
    omega
  | IB e =>
    refine ⟨h.1.1, ?_⟩
    have hl := h.1.2.1
    have hm := Nat.mul_le_mul_right (inverseB e (interchange p)).2 (hpow e)
    change (inverseB e (interchange p)).2 ≤ (inverseB e (interchange p)).1
    omega

theorem valid_iterations {s : Transformation} {p : ℕ × ℕ} (h : ValidOn s p) :
    iterations (s.inverse p).1 (s.inverse p).2 = iterations p.1 p.2 + 1 := by
  obtain ⟨hv, horder⟩ := valid_input h
  rw [iterations_of_ordered horder, run]
  simp only [dite_eq_right (Nat.ne_of_gt hv)]
  simp only [valid_step h]
  rw [iterations_of_ordered (valid_positive_ordered h).2]

/-- The four transformations exhaust actual nonterminal iterations. -/
theorem exists_valid_step {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    ∃ s : Transformation, s.ValidOn (step u v) ∧ s.inverse (step u v) = (u, v) := by
  obtain ⟨hl, hu⟩ := shift_bounds hv hvu
  by_cases ha : u - 2 ^ shift u v * v ≤ 2 ^ (shift u v + 1) * v - u
  · have hc : ChoosesA (shift u v) u v := ⟨hv, hl, hu, ha⟩
    rw [choosesA_step hc]
    have hinv : inverseA (shift u v) (v, u - 2 ^ shift u v * v) = (u, v) := by
      simp only [inverseA]
      congr 1
      omega
    by_cases hi : u - 2 ^ shift u v * v ≤ v
    · simp only [max_eq_left hi, min_eq_right hi]
      refine ⟨.A (shift u v), ?_, hinv⟩
      exact ⟨by simpa only [hinv] using hc, hi⟩
    · have hi' : v < u - 2 ^ shift u v * v := by omega
      simp only [max_eq_right (le_of_lt hi'), min_eq_left (le_of_lt hi')]
      refine ⟨.IA (shift u v), ?_, hinv⟩
      exact ⟨by simpa only [interchange, hinv] using hc, hi'⟩
  · have hb : 2 ^ (shift u v + 1) * v - u < u - 2 ^ shift u v * v := by omega
    have hc : ChoosesB (shift u v) u v := ⟨hv, hl, hu, hb⟩
    rw [choosesB_step hc]
    have hinv : inverseB (shift u v) (v, 2 ^ (shift u v + 1) * v - u) = (u, v) := by
      simp only [inverseB, Nat.sub_sub_self (le_of_lt hu)]
    by_cases hi : 2 ^ (shift u v + 1) * v - u ≤ v
    · simp only [max_eq_left hi, min_eq_right hi]
      refine ⟨.B (shift u v), ?_, hinv⟩
      exact ⟨by simpa only [hinv] using hc, hi⟩
    · have hi' : v < 2 ^ (shift u v + 1) * v - u := by omega
      simp only [max_eq_right (le_of_lt hi'), min_eq_left (le_of_lt hi')]
      refine ⟨.IB (shift u v), ?_, hinv⟩
      exact ⟨by simpa only [interchange, hinv] using hc, hi'⟩

end Transformation

/-- A valid partial computation contributes exactly one loop iteration per
step, regardless of whether its endpoint is terminal. -/
theorem partial_computation_iterations {ss : List Transformation} {p : ℕ × ℕ}
    (h : ValidComputation ss p) :
    iterations (inverseComputation ss p).1 (inverseComputation ss p).2 =
      iterations p.1 p.2 + ss.length := by
  induction ss generalizing p with
  | nil => simp [inverseComputation]
  | cons s ss ih =>
    simp only [inverseComputation, List.length_cons]
    rw [ih h.2, Transformation.valid_iterations h.1]
    omega

end Lsbgcd
