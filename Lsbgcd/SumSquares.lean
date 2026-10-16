module

public import Lsbgcd.Frontier
public import Lsbgcd.Reduction

@[expose] public section

/-!
# The sum-of-squares conjecture at the end of §6

Among ordered positive inputs taking exactly `n` iterations, the alternating
word ending in 1 minimises the sum of the squares of the two inputs.
The sequence is specified by the explicit recurrence printed on p. 484.
The paper calls it the numerator sequence of convergents to `√3`, but its
initial values and recurrence instead give the denominator sequence after
skipping the first convergent. `squareNumerator_sqrtThree_denominator` proves
the finite continued-fraction identity using the digits `[1; 1,2,1,2,…]`.
`SqrtThreeContinuedFraction.lean` proves that these fractions converge to `√3`.
-/
namespace Lsbgcd

/-- The squared Euclidean size of an input pair. -/
def squaredSize (p : ℕ × ℕ) : ℕ := p.1 ^ 2 + p.2 ^ 2

/-- The order used for the paper's reduction also controls squared size. -/
theorem smaller_squaredSize {p q : ℕ × ℕ} (hp : p.2 ≤ p.1)
    (h : Smaller p q) : squaredSize p ≤ squaredSize q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  obtain ⟨hx, hs⟩ := h
  dsimp [squaredSize] at *
  by_cases hy : y ≤ b
  · nlinarith
  · have hy' : b ≤ y := by omega
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hy'
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hp
    have ha : b + t + r + t ≤ a := by omega
    have hsq : (b + t + r + t) ^ 2 ≤ a ^ 2 := by nlinarith
    nlinarith

/-- Equality in squared size makes this reduction an equality of inputs. -/
theorem smaller_squaredSize_eq {p q : ℕ × ℕ} (hp : p.2 ≤ p.1)
    (h : Smaller p q) (he : squaredSize p = squaredSize q) : p = q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  obtain ⟨hx, hs⟩ := h
  dsimp [squaredSize] at *
  by_cases hy : y ≤ b
  · have hxa : x = a := by nlinarith
    have hyb : y = b := by nlinarith
    simp [hxa, hyb]
  · have hy' : b ≤ y := by omega
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hy'
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hp
    have ha : b + t + r + t ≤ a := by omega
    have hsq : (b + t + r + t) ^ 2 ≤ a ^ 2 := by nlinarith
    have ht : 0 < t := by omega
    exfalso
    nlinarith

/-- Alternating admissible word ending in 1, with exactly `n` digits. -/
def squareWord (n : ℕ) : List ℕ :=
  if n % 2 = 0 then repeat21 (n / 2) else repeat12 (n / 2) ++ [1]

/-- The proposed minimiser, extended to zero iterations by `(1,0)`. -/
def squareCandidate (n : ℕ) : ℕ × ℕ := convergent (squareWord n)

@[simp] theorem squareWord_even (k : ℕ) : squareWord (2 * k) = repeat21 k := by
  simp [squareWord]

@[simp] theorem squareWord_odd (k : ℕ) :
    squareWord (2 * k + 1) = repeat12 k ++ [1] := by
  simp [squareWord, Nat.add_mod, Nat.add_div]

theorem squareWord_admissible (n : ℕ) : Admissible (squareWord n) := by
  unfold squareWord
  split_ifs
  · exact admissible_repeat21 _
  · exact admissible_repeat12_append _ (Or.inl rfl)

theorem squareWord_length (n : ℕ) : (squareWord n).length = n := by
  unfold squareWord
  split_ifs <;> simp only [length_repeat21, length_repeat12, List.length_append,
    List.length_singleton] <;> omega

theorem squareCandidate_iterations (n : ℕ) :
    iterations (squareCandidate n).1 (squareCandidate n).2 = n := by
  rw [squareCandidate, admissible_iterations (squareWord_admissible n), squareWord_length]

theorem squareCandidate_ordered (n : ℕ) :
    0 < (squareCandidate n).1 ∧ (squareCandidate n).2 ≤ (squareCandidate n).1 :=
  admissible_convergent (squareWord_admissible n)

/-- Coefficients of `(M₂ M₁)^k = [[2r+s,2r],[r,s]]`. -/
private def squareCoeff : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => (3 * (squareCoeff k).1 + (squareCoeff k).2,
      2 * (squareCoeff k).1 + (squareCoeff k).2)

private theorem squareCoeff_positive (k : ℕ) :
    0 < (squareCoeff k).2 ∧ (0 < (squareCoeff k).1 ↔ 0 < k) := by
  induction k with
  | zero => norm_num [squareCoeff]
  | succ k ih => simp only [squareCoeff]; constructor <;> omega

private theorem square_repeat21 (k : ℕ) (as : List ℕ) :
    convergent (repeat21 k ++ as) =
      ((2 * (squareCoeff k).1 + (squareCoeff k).2) * (convergent as).1 +
        2 * (squareCoeff k).1 * (convergent as).2,
       (squareCoeff k).1 * (convergent as).1 +
        (squareCoeff k).2 * (convergent as).2) := by
  induction k with
  | zero => simp [repeat21, squareCoeff]
  | succ k ih =>
    simp only [repeat21, List.cons_append, convergent, squareCoeff, ih]
    congr 1 <;> ring

private theorem square_repeat12 (k : ℕ) (as : List ℕ) :
    convergent (repeat12 k ++ as) =
      ((2 * (squareCoeff k).1 + (squareCoeff k).2) * (convergent as).1 +
        (squareCoeff k).1 * (convergent as).2,
       2 * (squareCoeff k).1 * (convergent as).1 +
        (squareCoeff k).2 * (convergent as).2) := by
  induction k with
  | zero => simp [repeat12, squareCoeff]
  | succ k ih =>
    simp only [repeat12, List.cons_append, convergent, squareCoeff, ih]
    congr 1 <;> ring

/-- Exact cost of replacing an initial `(21)^i` by `(12)^i`.
The suffix `(21)^j` has convergent `(2d+t,d)`, where `t` is positive. -/
private theorem square_block_difference (i j : ℕ) :
    squaredSize (convergent (repeat12 i ++ repeat21 j)) =
      squaredSize (convergent (repeat21 (i + j))) +
        (squareCoeff i).1 ^ 2 *
          ((squareCoeff j).1 ^ 2 +
            8 * (squareCoeff j).1 * (squareCoeff j).2 +
            3 * (squareCoeff j).2 ^ 2) := by
  rw [repeat21_add, square_repeat12, square_repeat21]
  have hs := square_repeat21 j []
  simp only [List.append_nil, convergent, mul_one, mul_zero, add_zero] at hs
  rw [hs]
  simp only [squaredSize]
  ring

theorem square_block_minimal (i j : ℕ) :
    squaredSize (convergent (repeat21 (i + j))) ≤
      squaredSize (convergent (repeat12 i ++ repeat21 j)) := by
  rw [square_block_difference]
  omega

theorem square_block_eq_iff (i j : ℕ) :
    squaredSize (convergent (repeat12 i ++ repeat21 j)) =
      squaredSize (convergent (repeat21 (i + j))) ↔ i = 0 := by
  rw [square_block_difference]
  have hi := squareCoeff_positive i
  have hj := squareCoeff_positive j
  constructor
  · intro he
    have hz : (squareCoeff i).1 ^ 2 *
        ((squareCoeff j).1 ^ 2 +
          8 * (squareCoeff j).1 * (squareCoeff j).2 +
          3 * (squareCoeff j).2 ^ 2) = 0 := by omega
    have hp : 0 < (squareCoeff j).1 ^ 2 +
        8 * (squareCoeff j).1 * (squareCoeff j).2 +
        3 * (squareCoeff j).2 ^ 2 := by nlinarith
    have : (squareCoeff i).1 = 0 := by
      rcases Nat.mul_eq_zero.mp hz with h | h
      · nlinarith
      · omega
    omega
  · rintro rfl
    simp [squareCoeff]

/-- Global squared-size minimality among the admissible words of a fixed length. -/
theorem admissible_squaredSize_minimal {as : List ℕ} (h : Admissible as) :
    squaredSize (squareCandidate as.length) ≤ squaredSize (convergent as) := by
  rcases admissible_frontier as h with ⟨k, hk, hs⟩ | ⟨i, j, hij, hs⟩
  · rw [hk, squareCandidate, squareWord_odd]
    exact smaller_squaredSize
      (admissible_convergent (admissible_repeat12_append (as := [1]) k (Or.inl rfl))).2 hs
  · rw [hij, squareCandidate, squareWord_even]
    exact (square_block_minimal i j).trans (smaller_squaredSize
      (admissible_convergent (admissible_repeat12_append i (admissible_repeat21 j))).2 hs)

/-- Equality also determines the convergent, without a tie between inputs. -/
theorem admissible_squaredSize_eq {as : List ℕ} (h : Admissible as)
    (he : squaredSize (squareCandidate as.length) = squaredSize (convergent as)) :
    convergent as = squareCandidate as.length := by
  rcases admissible_frontier as h with ⟨k, hk, hs⟩ | ⟨i, j, hij, hs⟩
  · rw [hk, squareCandidate, squareWord_odd] at he ⊢
    exact (smaller_squaredSize_eq
      (admissible_convergent (admissible_repeat12_append (as := [1]) k (Or.inl rfl))).2 hs he).symm
  · rw [hij, squareCandidate, squareWord_even] at he ⊢
    have hle := smaller_squaredSize
      (admissible_convergent (admissible_repeat12_append i (admissible_repeat21 j))).2 hs
    have hmin := square_block_minimal i j
    have hi : i = 0 := (square_block_eq_iff i j).mp (by omega)
    subst i
    simp only [repeat12, List.nil_append, zero_add] at hs he ⊢
    exact (smaller_squaredSize_eq (admissible_convergent (admissible_repeat21 j)).2 hs he).symm

/-- The conjectured lower bound holds for every ordered nonzero input. -/
theorem sum_squares_lower_bound {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    squaredSize (squareCandidate (iterations u v)) ≤ u ^ 2 + v ^ 2 := by
  have hw := quotientWord_admissible u v hvu
  have hl : (quotientWord u v hvu).length = iterations u v := by
    rw [quotientWord_length, iterations_of_ordered hvu]
  have hm := admissible_squaredSize_minimal hw
  rw [hl] at hm
  exact hm.trans (smaller_squaredSize (admissible_convergent hw).2
    (quotientWord_smaller u v hu hvu))

/-- The minimum determines a unique ordered input pair. -/
theorem sum_squares_equality_iff {u v : ℕ} (hu : 0 < u) (hvu : v ≤ u) :
    u ^ 2 + v ^ 2 = squaredSize (squareCandidate (iterations u v)) ↔
      (u, v) = squareCandidate (iterations u v) := by
  constructor
  · intro he
    have hw := quotientWord_admissible u v hvu
    have hl : (quotientWord u v hvu).length = iterations u v := by
      rw [quotientWord_length, iterations_of_ordered hvu]
    have hm := admissible_squaredSize_minimal hw
    have hs := quotientWord_smaller u v hu hvu
    have hle := smaller_squaredSize (admissible_convergent hw).2 hs
    have heq : squaredSize (squareCandidate (quotientWord u v hvu).length) =
        squaredSize (convergent (quotientWord u v hvu)) := by
      rw [hl] at hm ⊢
      change squaredSize (convergent (quotientWord u v hvu)) ≤ u ^ 2 + v ^ 2 at hle
      omega
    have hp := admissible_squaredSize_eq hw heq
    have hq := smaller_squaredSize_eq (admissible_convergent hw).2 hs
      (show squaredSize (convergent (quotientWord u v hvu)) = squaredSize (u, v) by
        rw [← heq, hl, ← he]; rfl)
    rw [hl] at hp
    exact hq.symm.trans hp
  · intro he
    change squaredSize (u, v) = _
    rw [he]

/-- Successive candidates are obtained by alternating A₀ and A₁. -/
theorem squareWord_succ (n : ℕ) :
    squareWord (n + 1) = (if n % 2 = 0 then 1 else 2) :: squareWord n := by
  by_cases h : n % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    subst n
    simp [squareWord_even, squareWord_odd, repeat12_one]
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst n
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    simp [squareWord_even, squareWord_odd, repeat21, repeat12_one, Nat.add_mod]

theorem squareCandidate_succ (n : ℕ) :
    squareCandidate (n + 1) =
      ((if n % 2 = 0 then 1 else 2) * (squareCandidate n).1 + (squareCandidate n).2,
        (squareCandidate n).1) := by
  simp only [squareCandidate, squareWord_succ, convergent]

theorem squareCandidate_positive {n : ℕ} (hn : 0 < n) :
    0 < (squareCandidate n).2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [squareCandidate_succ]
  exact (squareCandidate_ordered k).1

/-- The explicit sequence `p₀ = 1, p₁ = 3` from the conjecture on p. 484.
The coefficient is 1 at even indices and 2 at odd indices. -/
def squareNumerator : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => (if n % 2 = 0 then 1 else 2) * squareNumerator (n + 1) + squareNumerator n

@[simp] theorem squareNumerator_zero : squareNumerator 0 = 1 := rfl
@[simp] theorem squareNumerator_one : squareNumerator 1 = 3 := rfl

/-- The even half of the paper's printed recurrence. -/
theorem squareNumerator_even (k : ℕ) :
    squareNumerator (2 * k + 2) = squareNumerator (2 * k + 1) + squareNumerator (2 * k) := by
  rw [squareNumerator]
  simp

/-- The odd half of the paper's printed recurrence. -/
theorem squareNumerator_odd (k : ℕ) :
    squareNumerator (2 * k + 3) =
      2 * squareNumerator (2 * k + 2) + squareNumerator (2 * k + 1) := by
  change squareNumerator ((2 * k + 1) + 2) = _
  rw [squareNumerator]
  simp [Nat.add_mod]

/-- The alternating candidates are precisely consecutive terms of the recurrence. -/
theorem squareCandidate_numerators (n : ℕ) :
    squareCandidate (n + 2) = (squareNumerator (n + 1), squareNumerator n) := by
  induction n with
  | zero => norm_num [squareCandidate, squareWord, repeat21, convergent, squareNumerator]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, squareCandidate_succ, ih]
    simp [squareNumerator]

private theorem squareWord_reverse (n : ℕ) :
    (squareWord n).reverse = (List.range n).map (fun k => if k % 2 = 0 then 1 else 2) := by
  induction n with
  | zero => simp [squareWord, repeat21]
  | succ n ih => simp [squareWord_succ, List.range_succ, ih]

/-- The recurrence terms are continuants of the alternating words. -/
theorem squareNumerator_continuant (n : ℕ) :
    continuant (squareWord (n + 1)) = squareNumerator n := by
  cases n with
  | zero => norm_num [continuant, squareWord, repeat12, convergent]
  | succ n =>
    simpa [squareCandidate, continuant] using
      congrArg Prod.fst (squareCandidate_numerators n)

/-- Correction to the prose on p. 484: `pₙ` is the denominator of the
truncation `[1; 1,2,1,2,…]` with `n+1` partial quotients after the semicolon.
These are the usual continued-fraction digits of `√3`. -/
theorem squareNumerator_sqrtThree_denominator (n : ℕ) :
    (convergent (1 :: (List.range (n + 1)).map
      (fun k => if k % 2 = 0 then 1 else 2))).2 = squareNumerator n := by
  rw [← squareWord_reverse, convergent_denominator, continuant_reverse,
    squareNumerator_continuant]

/-- Positive ordered input attaining the least squared size at exactly `n` iterations. -/
def IsSumSquaresMinimizer (n : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.2 ∧ p.2 ≤ p.1 ∧ iterations p.1 p.2 = n ∧
    ∀ u v : ℕ, 0 < v → v ≤ u → iterations u v = n → squaredSize p ≤ u ^ 2 + v ^ 2

theorem squareCandidate_minimizer {n : ℕ} (hn : 0 < n) :
    IsSumSquaresMinimizer n (squareCandidate n) := by
  refine ⟨squareCandidate_positive hn, (squareCandidate_ordered n).2,
    squareCandidate_iterations n, ?_⟩
  intro u v hv hvu hi
  have h := sum_squares_lower_bound (by omega : 0 < u) hvu
  rwa [hi] at h

/-- The sum-of-squares conjecture of §6, using its explicit printed recurrence. -/
theorem sum_squares_conjecture {n : ℕ} (hn : 2 ≤ n) :
    IsSumSquaresMinimizer n (squareNumerator (n - 1), squareNumerator (n - 2)) := by
  have h := squareCandidate_minimizer (show 0 < n by omega)
  have he := squareCandidate_numerators (n - 2)
  rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at he
  rwa [he] at h

/-- The minimiser is unique among ordered positive inputs. -/
theorem sum_squares_minimizer_unique {n : ℕ} {p : ℕ × ℕ}
    (h : IsSumSquaresMinimizer n p) : p = squareCandidate n := by
  obtain ⟨hv, hvu, hi, hm⟩ := h
  have hn : 0 < n := by
    rw [← hi, iterations_of_ordered hvu, run, dite_eq_right (Nat.ne_of_gt hv)]
    simp
  have hle := hm _ _ (squareCandidate_positive hn) (squareCandidate_ordered n).2
    (squareCandidate_iterations n)
  have hge := sum_squares_lower_bound (by omega : 0 < p.1) hvu
  rw [hi] at hge
  have he := (sum_squares_equality_iff (by omega : 0 < p.1) hvu).mp
    (by simpa [hi, squaredSize] using Nat.le_antisymm hle hge)
  simpa [hi] using he

/-- The positive-input boundary case not covered by `(pₙ₋₁,pₙ₋₂)`. -/
theorem sum_squares_one : IsSumSquaresMinimizer 1 (1, 1) := by
  simpa [squareCandidate, squareWord, repeat12, convergent] using
    (squareCandidate_minimizer (n := 1) (by decide))

end Lsbgcd
