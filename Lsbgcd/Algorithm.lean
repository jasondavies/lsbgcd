module

public import Mathlib

@[expose] public section

/-!
# The LSBGCD algorithm

Shallit and Sorenson, §1, p. 474. Natural subtraction is used only inside
the interval established by `shift_bounds`. Sorting implements the final
interchange in the pseudocode. The recursion decreases `u + v`, since
the larger coordinate need not decrease (for example on input `(1, 1)`).
-/

namespace Lsbgcd

/- `Challenge.lean` repeats `shift`, `remainder`, `step`, `run`, `gcd` and
`iterations` verbatim, together with the four lemmas `run`'s termination proof
uses: `shift_bounds`, `remainder_lt`, `step_ordered` and `step_decreases`.
Comparator requires both copies to elaborate to identical constants, so edit
them only in both files at once. Their proofs avoid `omega` deliberately: it
creates auxiliary lemmas named after the current module, which can never match
across the two modules. -/

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

theorem gcd_remainder {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    Nat.gcd v (remainder u v) = Nat.gcd u v := by
  obtain ⟨hlo, hhi⟩ := shift_bounds hv hvu
  unfold remainder
  rw [min_def]
  split_ifs with h
  · rw [Nat.gcd_sub_mul_right_right hlo, Nat.gcd_comm]
  · have hsum : (2 ^ (shift u v + 1) * v - u) + u =
        2 ^ (shift u v + 1) * v := Nat.sub_add_cancel (by omega)
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · have hd := Nat.gcd_dvd_right v (2 ^ (shift u v + 1) * v - u)
        have hm : Nat.gcd v (2 ^ (shift u v + 1) * v - u) ∣
            2 ^ (shift u v + 1) * v :=
          dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
        have := Nat.dvd_sub hm hd
        convert this using 1; omega
      · exact Nat.gcd_dvd_left _ _
    · apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_right _ _
      · exact Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_right u v) _)
          (Nat.gcd_dvd_left u v)

theorem gcd_step {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    Nat.gcd (step u v).1 (step u v).2 = Nat.gcd u v := by
  unfold step
  by_cases h : v ≤ remainder u v
  · simpa [max_eq_right h, min_eq_left h, Nat.gcd_comm] using gcd_remainder hv hvu
  · simpa [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h)]
      using gcd_remainder hv hvu

/-- Run on ordered inputs, returning the GCD and the exact iteration count. -/
def run (u v : ℕ) (_hvu : v ≤ u) : ℕ × ℕ :=
  if hv : v = 0 then (u, 0)
  else
    let next := step u v
    let result := run next.1 next.2 (step_ordered u v)
    (result.1, result.2 + 1)
termination_by u + v
decreasing_by exact step_decreases (Nat.pos_of_ne_zero hv) _hvu

theorem run_gcd (u v : ℕ) (hvu : v ≤ u) :
    (run u v hvu).1 = Nat.gcd u v := by
  rw [run]
  split_ifs with hv
  · simp [hv]
  · change (run (step u v).1 (step u v).2 (step_ordered u v)).1 = _
    rw [run_gcd, gcd_step (Nat.pos_of_ne_zero hv) hvu]
termination_by u + v
decreasing_by exact step_decreases (Nat.pos_of_ne_zero hv) hvu

/-- The value returned by the algorithm, after sorting the inputs. This is a
total interface, including zero inputs. -/
def gcd (u v : ℕ) : ℕ := (run (max u v) (min u v)
  (le_trans (min_le_left _ _) (le_max_left _ _))).1

/-- The number of loop iterations the algorithm performs, after sorting the inputs. -/
def iterations (u v : ℕ) : ℕ := (run (max u v) (min u v)
  (le_trans (min_le_left _ _) (le_max_left _ _))).2

theorem gcd_correct (u v : ℕ) : gcd u v = Nat.gcd u v := by
  unfold gcd
  rw [run_gcd]
  by_cases h : u ≤ v
  · simp [max_eq_right h, min_eq_left h, Nat.gcd_comm]
  · simp [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h)]

/-- Structurally recursive evaluator for kernel reduction of concrete examples. -/
def runFuel : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, u, _ => (u, 0)
  | fuel + 1, u, v =>
    if v = 0 then (u, 0)
    else
      let next := step u v
      let result := runFuel fuel next.1 next.2
      (result.1, result.2 + 1)

/-- The finite evaluator agrees with the terminating algorithm given enough fuel. -/
theorem runFuel_eq_run (fuel u v : ℕ) (hvu : v ≤ u) (hf : u + v ≤ fuel) :
    runFuel fuel u v = run u v hvu := by
  induction fuel generalizing u v with
  | zero =>
    have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u; subst v
    rw [run]
    rfl
  | succ fuel ih =>
    by_cases hv : v = 0
    · subst v
      rw [run]
      rfl
    · have hd := step_decreases (Nat.pos_of_ne_zero hv) hvu
      rw [runFuel, ite_eq_right hv, run, dite_eq_right hv]
      dsimp only
      rw [ih _ _ (step_ordered u v) (by omega)]

theorem iterations_eq_runFuel (u v : ℕ) :
    iterations u v = (runFuel (max u v + min u v) (max u v) (min u v)).2 := by
  unfold iterations
  rw [runFuel_eq_run _ _ _ (le_trans (min_le_left _ _) (le_max_left _ _)) (by omega)]

theorem iterations_of_ordered {u v : ℕ} (hvu : v ≤ u) :
    iterations u v = (run u v hvu).2 := by
  simp [iterations, max_eq_left hvu, min_eq_right hvu]

end Lsbgcd
