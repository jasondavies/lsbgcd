module

public import Lsbgcd

@[expose] public section

/-!
# Proved statements

Each declaration below has exactly the statement of its counterpart in
`Challenge.lean`. `gcd_correct`, `iterations_le_sharp_log` and
`sum_squares_conjecture` are proved under the same names in the library, so
importing `Lsbgcd` supplies them; the remaining statements are derived here
from `theorem1_1`, `isWorstCase_iff`, `ramharter_theorem` and
`sum_squares_minimizer_unique`.
-/

namespace Lsbgcd

theorem isWorstCase_unique {n : ℕ} {p q : ℕ × ℕ}
    (hp : IsWorstCase n p) (hq : IsWorstCase n q) : p = q :=
  ((isWorstCase_iff n p).1 hp).trans ((isWorstCase_iff n q).1 hq).symm

theorem worstCase_odd (n : ℕ) : ∃ x y : ℕ, IsWorstCase (2 * n + 1) (x, y) ∧
    (x : ℝ) = Real.sqrt 3 / 6 * (alpha ^ (n + 1) - beta ^ (n + 1)) ∧
    (y : ℝ) = Real.sqrt 3 / 6 *
      ((1 + Real.sqrt 3) * alpha ^ n - (1 - Real.sqrt 3) * beta ^ n) := by
  obtain ⟨h1, h2, -, -, -, -⟩ := theorem1_1.2.2.2 n
  exact ⟨_, _, theorem1_1.1 _, h1, h2⟩

theorem worstCase_four_mul (n : ℕ) : ∃ x y : ℕ, IsWorstCase (4 * n) (x, y) ∧
    (x : ℝ) = (2 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 ∧
    (y : ℝ) = (-2 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n)) / 12 := by
  obtain ⟨-, -, h1, h2, -, -⟩ := theorem1_1.2.2.2 n
  exact ⟨_, _, theorem1_1.1 _, h1, h2⟩

theorem worstCase_four_mul_add_two (n : ℕ) : ∃ x y : ℕ, IsWorstCase (4 * n + 2) (x, y) ∧
    (x : ℝ) = (4 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 2) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 2)) / 12 ∧
    (y : ℝ) = (-10 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 := by
  obtain ⟨-, -, -, -, h1, h2⟩ := theorem1_1.2.2.2 n
  exact ⟨_, _, theorem1_1.1 _, h1, h2⟩

theorem worstCase_order16 (x y : ℕ → ℕ) (h : ∀ n, IsWorstCase n (x n, y n)) :
    Order16 (fun n => (x n : ℤ)) ∧ Order16 (fun n => (y n : ℤ)) := by
  have hc (n : ℕ) : (x n, y n) = candidate n := (isWorstCase_iff n _).1 (h n)
  have hx : x = fun n => (candidate n).1 := funext fun n => congrArg Prod.fst (hc n)
  have hy : y = fun n => (candidate n).2 := funext fun n => congrArg Prod.snd (hc n)
  subst hx hy
  exact ⟨theorem1_1.2.1, theorem1_1.2.2.1⟩

theorem theorem5_1 (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b) (hs : bs.Pairwise (· ≤ ·)) :
    ((ramharterWord bs).Perm bs ∧
      ∀ as, as.Perm bs → continuant (ramharterWord bs) ≤ continuant as) ∧
    ∀ as, as.Perm bs →
      (continuant as = continuant (ramharterWord bs) ↔
        as = ramharterWord bs ∨ as = (ramharterWord bs).reverse) :=
  ramharter_theorem bs hpos hs

theorem sum_squares_minimizer_eq {n : ℕ} {p : ℕ × ℕ} (hn : 2 ≤ n)
    (h : IsSumSquaresMinimizer n p) :
    p = (sqrtThreeDenominator (n - 1), sqrtThreeDenominator (n - 2)) := by
  rw [sum_squares_minimizer_unique h]
  have he := squareCandidate_eq_sqrtThreeDenominator (n - 2)
  rwa [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at he

end Lsbgcd
