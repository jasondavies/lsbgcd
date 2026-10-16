module

public import Lsbgcd.Candidates

@[expose] public section

/-!
# Specifications for Theorem 1.1

The propositions in this module are specifications, not asserted theorems.
The recurrence and closed-form specifications are proved in MainRecurrence
and ClosedForms. Minimality proves global minimality and combines the
results into the unconditional theorem `theorem1_1`. No specification adds
an assumption to the verified library.

The positive first-coordinate convention excludes `(0,0)`; at n=0 the
paper's formulas give `(1,0)`, whereas allowing `(0,0)` would make it the
lexicographically least zero-iteration input.
-/
namespace Lsbgcd

def IsWorstCase (n : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.2 ≤ p.1 ∧ iterations p.1 p.2 = n ∧
    ∀ u v : ℕ, 0 < u → v ≤ u → iterations u v = n → LexLE p (u, v)

/-- The global minimality claim proved in Minimality.lean via §§3–5. -/
def CandidateMinimality : Prop := ∀ n : ℕ, IsWorstCase n (candidate n)

/-- The consequence of Theorem 4.3 proved in Reduction.lean: every actual
input admits an admissible word of the same length with no larger input. -/
def ReductionToAdmissible : Prop := ∀ u v : ℕ, 0 < u → v ≤ u →
  ∃ as : List ℕ, Admissible as ∧ as.length = iterations u v ∧
    LexLE (convergent as) (u, v)

/-- The lexicographic continuant minimisation claim of §§5–6, including
the denominator tie-break. This is stronger than minimising the numerator. -/
def AdmissibleMinimality : Prop := ∀ as : List ℕ, Admissible as →
  LexLE (candidate as.length) (convergent as)

/-- Expanded recurrence for the order-16 polynomial in Theorem 1.1. -/
def Order16 (f : ℕ → ℤ) : Prop := ∀ n : ℕ,
  f (n + 16) - 4 * f (n + 14) - 14 * f (n + 12) + 60 * f (n + 10) -
    60 * f (n + 6) + 14 * f (n + 4) + 4 * f (n + 2) - f n = 0

noncomputable def alpha : ℝ := 2 + Real.sqrt 3
noncomputable def beta : ℝ := 2 - Real.sqrt 3

/-- The six displayed formulas in Theorem 1.1 (p. 474). -/
def ClosedForms : Prop := ∀ n : ℕ,
  (candidate (2 * n + 1)).1 =
    Real.sqrt 3 / 6 * (alpha ^ (n + 1) - beta ^ (n + 1)) ∧
  (candidate (2 * n + 1)).2 =
    Real.sqrt 3 / 6 * ((1 + Real.sqrt 3) * alpha ^ n - (1 - Real.sqrt 3) * beta ^ n) ∧
  (candidate (4 * n)).1 =
    (2 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 1)) / 12 ∧
  (candidate (4 * n)).2 =
    (-2 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n)) / 12 ∧
  (candidate (4 * n + 2)).1 =
    (4 + (4 - Real.sqrt 3) * alpha ^ (2 * n + 2) +
      (4 + Real.sqrt 3) * beta ^ (2 * n + 2)) / 12 ∧
  (candidate (4 * n + 2)).2 =
    (-10 + (1 + 3 * Real.sqrt 3) * alpha ^ (2 * n + 1) +
      (1 - 3 * Real.sqrt 3) * beta ^ (2 * n + 1)) / 12

/-- The statement of Theorem 1.1, proved unconditionally in Minimality.lean. -/
def MainTheorem : Prop :=
  CandidateMinimality ∧
  Order16 (fun n => (candidate n).1) ∧
  Order16 (fun n => (candidate n).2) ∧
  ClosedForms

end Lsbgcd
