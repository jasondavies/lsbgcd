module

public import Lsbgcd.Continuants

@[expose] public section

/-! # Matrix calculations from §6 -/
namespace Lsbgcd

def m1 : Mat := digitMatrix 1
def m2 : Mat := digitMatrix 2

/-- The operation M ↦ M₁ M₂ M M₂ M₁ used in both even cases. -/
def sandwich (m : Mat) : Mat := m1 * m2 * m * m2 * m1

theorem sandwich_entries (m : Mat) :
    sandwich m = !![
      9 * m 0 0 + 3 * m 0 1 + 3 * m 1 0 + m 1 1,
      6 * m 0 0 + 3 * m 0 1 + 2 * m 1 0 + m 1 1;
      6 * m 0 0 + 2 * m 0 1 + 3 * m 1 0 + m 1 1,
      4 * m 0 0 + 2 * m 0 1 + 2 * m 1 0 + m 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sandwich, m1, m2, digitMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

/-- The cubic identity computed in §6, valid for every starting matrix. -/
theorem sandwich_cubic (m : Mat) :
    sandwich (sandwich (sandwich m)) =
      (15 : ℤ) • sandwich (sandwich m) - (15 : ℤ) • sandwich m + m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sandwich_entries, Matrix.add_apply] <;> ring

def orbit (initial : Mat) : ℕ → Mat
  | 0 => initial
  | n + 1 => sandwich (orbit initial n)

theorem orbit_powers (initial : Mat) (n : ℕ) :
    orbit initial n = (m1 * m2) ^ n * initial * (m2 * m1) ^ n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit, ih, pow_succ', pow_succ]
    simp only [sandwich]
    noncomm_ring

/-- Simultaneously proves the recurrences for C,D,E,F and R,S,T,U. -/
theorem orbit_recurrence (initial : Mat) (n : ℕ) :
    orbit initial (n + 3) = (15 : ℤ) • orbit initial (n + 2) -
      (15 : ℤ) • orbit initial (n + 1) + orbit initial n := by
  exact sandwich_cubic (orbit initial n)

def evenMatrix (n : ℕ) : Mat := orbit 1 n
def offsetMatrix (n : ℕ) : Mat := orbit (m2 * m1) n

theorem evenMatrix_powers (n : ℕ) :
    evenMatrix n = (m1 * m2) ^ n * (m2 * m1) ^ n := by
  simp [evenMatrix, orbit_powers]

/-- Equation (6.2). -/
theorem offsetMatrix_powers (n : ℕ) :
    offsetMatrix n = (m1 * m2) ^ n * (m2 * m1) ^ (n + 1) := by
  rw [offsetMatrix, orbit_powers, pow_succ']
  simp [Matrix.mul_assoc]

theorem sandwich_off_diagonal (m : Mat) :
    sandwich m 0 1 - sandwich m 1 0 = m 0 1 - m 1 0 := by
  simp [sandwich_entries]
  ring

/-- The denominator tie-break in the n ≡ 2 mod 4 case: S_k − T_k = 1. -/
theorem offset_off_diagonal (n : ℕ) :
    offsetMatrix n 0 1 - offsetMatrix n 1 0 = 1 := by
  induction n with
  | zero => norm_num [offsetMatrix, orbit, m1, m2, digitMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  | succ n ih =>
    change sandwich (orbit (m2 * m1) n) 0 1 -
      sandwich (orbit (m2 * m1) n) 1 0 = 1
    rw [sandwich_off_diagonal]
    exact ih

theorem offset_denominator_lt (n : ℕ) : offsetMatrix n 1 0 < offsetMatrix n 0 1 := by
  have := offset_off_diagonal n
  omega

/-- Factorisation of the order-16 characteristic polynomial in Theorem 1.1. -/
theorem characteristic_factorisation (z : ℤ) :
    (z ^ 12 - 15 * z ^ 8 + 15 * z ^ 4 - 1) * (z ^ 4 - 4 * z ^ 2 + 1) =
      (z - 1) * (z + 1) * (z ^ 2 + 1) * (z ^ 4 - 4 * z ^ 2 + 1) ^ 2 *
        (z ^ 4 + 4 * z ^ 2 + 1) := by ring

end Lsbgcd
