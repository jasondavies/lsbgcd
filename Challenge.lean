module

public import Mathlib

@[expose] public section

/-!
# Advertised statements

Jeffrey Shallit and Jonathan Sorenson, *Analysis of a Left-Shift Binary GCD
Algorithm*, Journal of Symbolic Computation 17 (1994), 473–486.

This file is the statement surface to audit. It defines the algorithm of §1
exactly as the proof development does, then states:

* correctness of the algorithm (§1);
* Theorem 1.1: for each `n`, the lexicographically least ordered input that
  takes exactly `n` iterations, its six closed forms, and the order-16
  recurrence satisfied by both coordinates;
* Theorem 5.1, Ramharter's characterisation of the permutations of a list of
  positive digits that minimise the continuant;
* the sharp logarithmic iteration bound of §7;
* the sum-of-squares conjecture stated at the end of §6, with uniqueness.

The definitions below are copied verbatim from `Lsbgcd/Algorithm.lean`,
`Lsbgcd/Steps.lean`, `Lsbgcd/Specification.lean`, `Lsbgcd/Continuants.lean`,
`Lsbgcd/Ramharter.lean` and `Lsbgcd/SumSquares.lean`;
Comparator checks that they are the same constants as in the solution.
The four supporting lemmas are needed only for termination of `run`.
-/

namespace Lsbgcd

/-! ## The algorithm (§1, p. 474) -/

/-- The exponent `e = ⌊log₂ (u / v)⌋` selected in the main loop, so that
`2^e v ≤ u < 2^(e+1) v` when `0 < v ≤ u`. -/
def shift (u v : ℕ) : ℕ := Nat.log 2 (u / v)

theorem shift_bounds {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    2 ^ shift u v * v ≤ u ∧ u < 2 ^ (shift u v + 1) * v := by
  have hq : u / v ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp ((Nat.le_div_iff_mul_le hv).2 (by simpa using hvu))
  constructor
  · exact (Nat.le_div_iff_mul_le hv).1 (Nat.pow_log_le_self 2 hq)
  · exact (Nat.div_lt_iff_lt_mul hv).1 (Nat.lt_pow_succ_log_self (by decide) _)

/-- The least distance from `u` to the two adjacent shifted multiples
`2^e v` and `2^(e+1) v`. -/
def remainder (u v : ℕ) : ℕ :=
  min (u - 2 ^ shift u v * v) (2 ^ (shift u v + 1) * v - u)

/-- One loop iteration: replace `(u, v)` by `(v, remainder u v)`, then
interchange if necessary so that the first coordinate is the larger. -/
def step (u v : ℕ) : ℕ × ℕ :=
  (max v (remainder u v), min v (remainder u v))

theorem remainder_lt {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    remainder u v < u := by
  have hb := (shift_bounds hv hvu).1
  have hp : 0 < 2 ^ shift u v * v := Nat.mul_pos (Nat.pow_pos (by decide)) hv
  exact lt_of_le_of_lt (min_le_left _ _) (Nat.sub_lt (lt_of_lt_of_le hp hb) hp)

theorem step_ordered (u v : ℕ) : (step u v).2 ≤ (step u v).1 :=
  le_trans (min_le_left _ _) (le_max_left _ _)

theorem step_decreases {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    (step u v).1 + (step u v).2 < u + v := by
  have h := remainder_lt hv hvu
  simp only [step, max_add_min]
  rw [Nat.add_comm u v]
  exact Nat.add_lt_add_left h v

/-- Run on ordered inputs, returning the GCD and the exact iteration count. -/
def run (u v : ℕ) (_hvu : v ≤ u) : ℕ × ℕ :=
  if hv : v = 0 then (u, 0)
  else
    let next := step u v
    let result := run next.1 next.2 (step_ordered u v)
    (result.1, result.2 + 1)
termination_by u + v
decreasing_by exact step_decreases (Nat.pos_of_ne_zero hv) _hvu

/-- The value returned by the algorithm, after sorting the inputs. -/
def gcd (u v : ℕ) : ℕ := (run (max u v) (min u v)
  (le_trans (min_le_left _ _) (le_max_left _ _))).1

/-- The number of loop iterations the algorithm performs, after sorting the inputs. -/
def iterations (u v : ℕ) : ℕ := (run (max u v) (min u v)
  (le_trans (min_le_left _ _) (le_max_left _ _))).2

/-! ## Worst-case inputs (Theorem 1.1) -/

/-- Lexicographic order on pairs: first coordinates, then second coordinates. -/
def LexLE (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- `p = (u, v)` with `0 ≤ v ≤ u` and `0 < u` takes exactly `n` iterations and is
lexicographically least among all such inputs: the paper's `(xₙ, yₙ)`. -/
def IsWorstCase (n : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.2 ≤ p.1 ∧ iterations p.1 p.2 = n ∧
    ∀ u v : ℕ, 0 < u → v ≤ u → iterations u v = n → LexLE p (u, v)

/-- Expanded recurrence for the order-16 polynomial in Theorem 1.1. -/
def Order16 (f : ℕ → ℤ) : Prop := ∀ n : ℕ,
  f (n + 16) - 4 * f (n + 14) - 14 * f (n + 12) + 60 * f (n + 10) -
    60 * f (n + 6) + 14 * f (n + 4) + 4 * f (n + 2) - f n = 0

/-- `α = 2 + √3`. The closed forms of Theorem 1.1 are written in powers of `α`
and `β`, the two roots of `x² − 4x + 1`. -/
noncomputable def alpha : ℝ := 2 + Real.sqrt 3
/-- `β = 2 − √3 = 1 / α`. -/
noncomputable def beta : ℝ := 2 - Real.sqrt 3

/-! ## Continuants and Ramharter's permutation theorem (§5, Theorem 5.1) -/

/-- Numerator and denominator of the finite continued fraction
`a₀ + 1/(a₁ + 1/(⋯ + 1/aₖ))`, by recursion on the first digit: if the tail has
numerator `p` and denominator `q`, the whole word has `(a₀ p + q, p)`.
The empty word gives `(1, 0)`. -/
def convergent : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | a :: as =>
    let p := convergent as
    (a * p.1 + p.2, p.1)

/-- The continuant `K(a₀, …, aₖ)`: the numerator of `convergent`. -/
def continuant (as : List ℕ) : ℕ := (convergent as).1

/-- `ramharterIndices lo n` arranges the `n` ranks `lo, …, hi`, where
`hi = lo + n − 1`, in the minimising order. For `n ≥ 4` it is
`lo, hi, (ramharterIndices (lo + 2) (n − 4)), hi − 1, lo + 1`; that is, the two
least and two greatest remaining ranks are placed at the ends and the rule
recurses inward. This recursion gives all three cases of the paper's displayed
formula for Theorem 5.1. -/
def ramharterIndices (lo : ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => [lo]
  | 2 => [lo, lo + 1]
  | 3 => [lo, lo + 2, lo + 1]
  | n + 4 => lo :: (lo + n + 3) :: ramharterIndices (lo + 2) n ++
      [lo + n + 2, lo + 1]

/-- Apply the rank arrangement to a sorted list. The use of `getD` makes
this a total definition; every rank is less than `bs.length`, so the default
is never used. -/
def ramharterWord (bs : List ℕ) : List ℕ :=
  (ramharterIndices 0 bs.length).map (fun i => bs.getD i 0)

/-! ## Sum of squares (end of §6, p. 484) -/

/-- The squared Euclidean size of an input pair. -/
def squaredSize (p : ℕ × ℕ) : ℕ := p.1 ^ 2 + p.2 ^ 2

/-- The explicit sequence `p₀ = 1, p₁ = 3` from the conjecture on p. 484.
The coefficient is 1 at even indices and 2 at odd indices. -/
def squareNumerator : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => (if n % 2 = 0 then 1 else 2) * squareNumerator (n + 1) + squareNumerator n

/-- Positive ordered input attaining the least squared size at exactly `n` iterations. -/
def IsSumSquaresMinimizer (n : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.2 ∧ p.2 ≤ p.1 ∧ iterations p.1 p.2 = n ∧
    ∀ u v : ℕ, 0 < v → v ≤ u → iterations u v = n → squaredSize p ≤ u ^ 2 + v ^ 2

/-! ## Statements -/

/-- §1: the algorithm computes the greatest common divisor. -/
theorem gcd_correct (u v : ℕ) : gcd u v = Nat.gcd u v := by
  sorry

/-- The least input taking `n` iterations is unique. -/
theorem isWorstCase_unique {n : ℕ} {p q : ℕ × ℕ}
    (hp : IsWorstCase n p) (hq : IsWorstCase n q) : p = q := by
  sorry

/-- Theorem 1.1, odd case: `(x_{2n+1}, y_{2n+1})`. -/
theorem worstCase_odd (n : ℕ) : ∃ x y : ℕ, IsWorstCase (2 * n + 1) (x, y) ∧
    (x : ℝ) = Real.sqrt 3 / 6 * (alpha ^ (n + 1) - beta ^ (n + 1)) ∧
    (y : ℝ) = Real.sqrt 3 / 6 *
      ((1 + Real.sqrt 3) * alpha ^ n - (1 - Real.sqrt 3) * beta ^ n) := by
  sorry

/-- Theorem 1.1, case `4n`: `(x_{4n}, y_{4n})`. At `n = 0` this is `(1, 0)`. -/
theorem worstCase_four_mul (n : ℕ) : ∃ x y : ℕ, IsWorstCase (4 * n) (x, y) ∧
    (x : ℝ) = (2 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 ∧
    (y : ℝ) = (-2 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n)) / 12 := by
  sorry

/-- Theorem 1.1, case `4n + 2`: `(x_{4n+2}, y_{4n+2})`. -/
theorem worstCase_four_mul_add_two (n : ℕ) : ∃ x y : ℕ, IsWorstCase (4 * n + 2) (x, y) ∧
    (x : ℝ) = (4 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 2) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 2)) / 12 ∧
    (y : ℝ) = (-10 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 := by
  sorry

/-- Theorem 1.1: both worst-case sequences satisfy the order-16 recurrence
with characteristic polynomial `x¹⁶ − 4x¹⁴ − 14x¹² + 60x¹⁰ − 60x⁶ + 14x⁴ + 4x² − 1`. -/
theorem worstCase_order16 (x y : ℕ → ℕ) (h : ∀ n, IsWorstCase n (x n, y n)) :
    Order16 (fun n => (x n : ℤ)) ∧ Order16 (fun n => (y n : ℤ)) := by
  sorry

/-- Theorem 5.1 (Ramharter): for positive digits `b₁ ≤ ⋯ ≤ bₖ`, `ramharterWord`
is a permutation minimising the continuant over all permutations, and a
permutation attains the minimum exactly when it is that word or its reverse.
Repeated digits are allowed. -/
theorem theorem5_1 (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b) (hs : bs.Pairwise (· ≤ ·)) :
    ((ramharterWord bs).Perm bs ∧
      ∀ as, as.Perm bs → continuant (ramharterWord bs) ≤ continuant as) ∧
    ∀ as, as.Perm bs →
      (continuant as = continuant (ramharterWord bs) ↔
        as = ramharterWord bs ∨ as = (ramharterWord bs).reverse) := by
  sorry

/-- §7: the sharp bound `iterations u v ≤ log_{√(2+√3)} u + O(1)`, with an
explicit additive constant. -/
theorem iterations_le_sharp_log {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    (iterations u v : ℝ) ≤ 2 / Real.log alpha * Real.log u +
      (2 * Real.log 3 / Real.log alpha + 1) := by
  sorry

/-- End of §6: for `n ≥ 2`, `(pₙ₋₁, pₙ₋₂)` minimises `u² + v²` among ordered
positive inputs taking exactly `n` iterations. -/
theorem sum_squares_conjecture {n : ℕ} (hn : 2 ≤ n) :
    IsSumSquaresMinimizer n (squareNumerator (n - 1), squareNumerator (n - 2)) := by
  sorry

/-- The sum-of-squares minimiser is unique. -/
theorem sum_squares_minimizer_eq {n : ℕ} {p : ℕ × ℕ} (hn : 2 ≤ n)
    (h : IsSumSquaresMinimizer n p) :
    p = (squareNumerator (n - 1), squareNumerator (n - 2)) := by
  sorry

end Lsbgcd
