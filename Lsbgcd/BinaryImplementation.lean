import Lsbgcd.Complexity

/-!
# Selecting the shift from binary lengths

The implementation observation on p. 474 is made precise here: the selected
exponent is the difference of the leading-bit positions, possibly reduced by
one comparison. This computes the same exponent as the specification's
integer-division formula, without performing integer division.
-/
namespace Lsbgcd

/-- The difference of the leading-bit positions. -/
def lengthShift (u v : ℕ) : ℕ := Nat.log 2 u - Nat.log 2 v

/-- Shift selection using binary lengths and one comparison. -/
def shiftByLengths (u v : ℕ) : ℕ :=
  let k := lengthShift u v
  if 2 ^ k * v ≤ u then k else k - 1

theorem lengthShift_approximates {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    2 ^ lengthShift u v * v < 2 * u ∧ u < 2 * (2 ^ lengthShift u v * v) := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hlogs : Nat.log 2 v ≤ Nat.log 2 u := Nat.log_mono_right hvu
  have hp : 2 ^ lengthShift u v * 2 ^ Nat.log 2 v = 2 ^ Nat.log 2 u := by
    exact Nat.pow_sub_mul_pow 2 hlogs
  have hvlo := Nat.pow_log_le_self 2 (ne_of_gt hv)
  have hvhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) v
  have hulo := Nat.pow_log_le_self 2 (ne_of_gt hu)
  have huhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) u
  rw [pow_succ] at hvhi huhi
  have hpos : 0 < 2 ^ lengthShift u v := by positivity
  have hmlo := Nat.mul_le_mul_left (2 ^ lengthShift u v) hvlo
  have hmhi := Nat.mul_lt_mul_of_pos_left hvhi hpos
  constructor <;> nlinarith

/-- The length-based exponent satisfies the required adjacent-power interval. -/
theorem shiftByLengths_bounds {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    2 ^ shiftByLengths u v * v ≤ u ∧ u < 2 ^ (shiftByLengths u v + 1) * v := by
  obtain ⟨hlo, hhi⟩ := lengthShift_approximates hv hvu
  unfold shiftByLengths
  dsimp only
  split_ifs with h
  · constructor
    · exact h
    · rw [pow_succ]
      nlinarith
  · have hk : 1 ≤ lengthShift u v := by
      by_contra hk
      have hk0 : lengthShift u v = 0 := by omega
      simp only [hk0, pow_zero, one_mul] at h
      exact h hvu
    have hp : 2 ^ (lengthShift u v - 1) * 2 = 2 ^ lengthShift u v := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    constructor
    · nlinarith
    · rw [Nat.sub_add_cancel hk]
      omega

/-- The binary-length implementation selects exactly the specified exponent. -/
theorem shiftByLengths_eq_shift {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    shiftByLengths u v = shift u v := by
  obtain ⟨hlo, hhi⟩ := shiftByLengths_bounds hv hvu
  symm
  exact Nat.log_eq_of_pow_le_of_lt_pow
    ((Nat.le_div_iff_mul_le hv).2 hlo)
    ((Nat.div_lt_iff_lt_mul hv).2 hhi)

/-- A loop step using the division-free exponent selector. -/
def binaryStep (u v : ℕ) : ℕ × ℕ :=
  let e := shiftByLengths u v
  let t := min (u - 2 ^ e * v) (2 ^ (e + 1) * v - u)
  (max v t, min v t)

theorem binaryStep_eq_step {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    binaryStep u v = step u v := by
  simp only [binaryStep, shiftByLengths_eq_shift hv hvu, step, remainder]

end Lsbgcd
