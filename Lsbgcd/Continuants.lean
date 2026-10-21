module

public import Mathlib

@[expose] public section

/-! # Continuants and continued-fraction numerators (§5) -/
namespace Lsbgcd

/-- Numerator and denominator of the finite continued fraction
`a₀ + 1/(a₁ + 1/(⋯ + 1/aₖ))`, by recursion on the first digit: if the tail has
numerator `p` and denominator `q`, the whole word has `(a₀ p + q, p)`.
The empty word gives `(1, 0)`, the terminal inverse computation. -/
def convergent : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | a :: as =>
    let p := convergent as
    (a * p.1 + p.2, p.1)

/-- The continuant `K(a₀, …, aₖ)`: the numerator of `convergent`. -/
def continuant (as : List ℕ) : ℕ := (convergent as).1

@[simp] theorem continuant_nil : continuant [] = 1 := rfl
@[simp] theorem continuant_singleton (a : ℕ) : continuant [a] = a := by
  simp [continuant, convergent]

theorem continuant_cons_cons (a b : ℕ) (as : List ℕ) :
    continuant (a :: b :: as) = a * continuant (b :: as) + continuant as := rfl

/-- The denominator is the continuant of the tail, as in §5. -/
theorem convergent_denominator (a : ℕ) (as : List ℕ) :
    (convergent (a :: as)).2 = continuant as := rfl

theorem convergent_coprime (as : List ℕ) :
    Nat.Coprime (convergent as).1 (convergent as).2 := by
  induction as with
  | nil => decide
  | cons a as ih =>
    change Nat.gcd (a * (convergent as).1 + (convergent as).2)
      (convergent as).1 = 1
    rw [Nat.add_comm, Nat.mul_comm a, Nat.gcd_add_mul_left_left, Nat.gcd_comm]
    exact ih

/-- A 2×2 continuant matrix over the integers. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

/-- The matrix `[[a, 1], [1, 0]]` of one partial quotient. -/
def digitMatrix (a : ℕ) : Mat := !![(a : ℤ), 1; 1, 0]

/-- The product of the digit matrices of a word; its first column is the
convergent (`wordMatrix_first_column`). -/
def wordMatrix : List ℕ → Mat
  | [] => 1
  | a :: as => digitMatrix a * wordMatrix as

theorem wordMatrix_append (as bs : List ℕ) :
    wordMatrix (as ++ bs) = wordMatrix as * wordMatrix bs := by
  induction as with
  | nil => simp [wordMatrix]
  | cons a as ih => simp [wordMatrix, ih, Matrix.mul_assoc]

theorem wordMatrix_reverse (as : List ℕ) :
    wordMatrix as.reverse = (wordMatrix as).transpose := by
  induction as with
  | nil => simp [wordMatrix]
  | cons a as ih =>
    simp only [List.reverse_cons, wordMatrix_append, ih, wordMatrix, mul_one,
      Matrix.transpose_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- First-column form of the matrix identity (6.1). -/
theorem wordMatrix_first_column (as : List ℕ) :
    wordMatrix as 0 0 = (convergent as).1 ∧
      wordMatrix as 1 0 = (convergent as).2 := by
  induction as with
  | nil => norm_num [wordMatrix, convergent]
  | cons a as ih =>
    simp [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      convergent, ih.1, ih.2, Nat.cast_add, Nat.cast_mul]

theorem wordMatrix_second_column (as : List ℕ) (b : ℕ) :
    wordMatrix (as ++ [b]) 0 1 = (convergent as).1 ∧
      wordMatrix (as ++ [b]) 1 1 = (convergent as).2 := by
  simp [wordMatrix_append, wordMatrix, digitMatrix, Matrix.mul_apply,
    Fin.sum_univ_two, (wordMatrix_first_column as).1, (wordMatrix_first_column as).2]

/-- The complete four-entry identity (6.1), with at least two digits so
the middle continuant is defined by the ordinary empty-word convention. -/
theorem matrix_identity6_1 (a b : ℕ) (as : List ℕ) :
    wordMatrix (a :: (as ++ [b])) = !![
      (continuant (a :: (as ++ [b])) : ℤ), (continuant (a :: as) : ℤ);
      (continuant (as ++ [b]) : ℤ), (continuant as : ℤ)] := by
  have hfirst := wordMatrix_first_column (a :: (as ++ [b]))
  have hsecond := wordMatrix_second_column (a :: as) b
  ext i j
  fin_cases i <;> fin_cases j
  · exact hfirst.1
  · exact hsecond.1
  · exact hfirst.2
  · exact hsecond.2

/-- Reversal symmetry, equation (5.3). -/
theorem continuant_reverse (as : List ℕ) : continuant as.reverse = continuant as := by
  have h1 := (wordMatrix_first_column as.reverse).1
  have h2 := (wordMatrix_first_column as).1
  rw [wordMatrix_reverse] at h1
  simp only [Matrix.transpose_apply] at h1
  unfold continuant
  exact_mod_cast h1.symm.trans h2

/-- The paper's right-end recurrence (5.2). -/
theorem continuant_append_pair (as : List ℕ) (a b : ℕ) :
    continuant (as ++ [a, b]) = b * continuant (as ++ [a]) + continuant as := by
  rw [← continuant_reverse (as ++ [a, b])]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, continuant_cons_cons]
  rw [← continuant_reverse (as ++ [a])]
  simp [continuant_reverse]

/-- Words over {1,2} with no adjacent 1s, the set P_n of §5. -/
def Admissible : List ℕ → Prop
  | [] => True
  | [a] => a = 1 ∨ a = 2
  | a :: b :: as => (a = 1 ∨ a = 2) ∧ ¬(a = 1 ∧ b = 1) ∧ Admissible (b :: as)

end Lsbgcd
