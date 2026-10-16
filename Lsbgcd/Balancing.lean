module

public import Lsbgcd.Candidates

@[expose] public section

/-! # Balancing the two alternating blocks in the even extremal words -/
namespace Lsbgcd

/-- The even-length words after the local exchange reductions. -/
def blockWord (i j : ℕ) : List ℕ := repeat12 i ++ repeat21 j

def blockMatrix (i j : ℕ) : Mat := (m1 * m2) ^ i * (m2 * m1) ^ j

theorem blockWord_matrix (i j : ℕ) : wordMatrix (blockWord i j) = blockMatrix i j := by
  simp [blockWord, blockMatrix, wordMatrix_append, wordMatrix_repeat12, wordMatrix_repeat21]

theorem blockMatrix_column (i j : ℕ) :
    blockMatrix i j 0 0 = (convergent (blockWord i j)).1 ∧
    blockMatrix i j 1 0 = (convergent (blockWord i j)).2 := by
  rw [← blockWord_matrix]
  exact wordMatrix_first_column _

private theorem alternating_commutator :
    (m1 * m2) * (m2 * m1 - m1 * m2) * (m2 * m1) = m2 * m1 - m1 * m2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m1, m2, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem alternating_commutator_powers (i : ℕ) :
    (m1 * m2) ^ i * (m2 * m1 - m1 * m2) * (m2 * m1) ^ i =
      m2 * m1 - m1 * m2 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ']
    calc
      (m1 * m2) ^ i * (m1 * m2) * (m2 * m1 - m1 * m2) *
          ((m2 * m1) * (m2 * m1) ^ i) =
        (m1 * m2) ^ i * ((m1 * m2) * (m2 * m1 - m1 * m2) * (m2 * m1)) *
          (m2 * m1) ^ i := by noncomm_ring
      _ = _ := by rw [alternating_commutator, ih]

/-- Moving a block toward the shorter side has a difference independent of
    the common length of the two sides. -/
theorem blockMatrix_exchange (i d : ℕ) :
    blockMatrix i (i + d + 1) - blockMatrix (i + 1) (i + d) =
      (m2 * m1 - m1 * m2) * (m2 * m1) ^ d := by
  unfold blockMatrix
  rw [show i + d + 1 = i + 1 + d by omega,
    pow_add (m2 * m1) (i + 1) d, pow_succ' (m2 * m1) i,
    pow_succ (m1 * m2) i, pow_add (m2 * m1) i d]
  calc
    _ = ((m1 * m2) ^ i * (m2 * m1 - m1 * m2) * (m2 * m1) ^ i) *
        (m2 * m1) ^ d := by noncomm_ring
    _ = _ := by rw [alternating_commutator_powers]

private theorem blockMatrix_succ (i j : ℕ) :
    blockMatrix (i + 1) (j + 1) = sandwich (blockMatrix i j) := by
  simp only [blockMatrix, pow_succ' (m1 * m2), pow_succ (m2 * m1), sandwich]
  noncomm_ring

private theorem blockMatrix_transpose (i j : ℕ) :
    (blockMatrix i j).transpose = blockMatrix j i := by
  have h1 : m1.transpose = m1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h2 : m2.transpose = m2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp [blockMatrix, Matrix.transpose_mul, Matrix.transpose_pow, h1, h2]

private theorem alternating_nonneg (d : ℕ) : 0 ≤ ((m2 * m1) ^ d) 1 0 := by
  rw [← wordMatrix_repeat21, (wordMatrix_first_column _).2]
  positivity

private theorem alternating_positive (d : ℕ) : 0 < ((m2 * m1) ^ (d + 1)) 1 0 := by
  rw [← wordMatrix_repeat21, (wordMatrix_first_column _).2]
  have h := (admissible_convergent (admissible_repeat21 d)).1
  simp only [repeat21, convergent, one_mul]
  exact_mod_cast (by omega : 0 < (convergent (repeat21 d)).1 + (convergent (repeat21 d)).2)

private theorem alternating_off_diagonal (d : ℕ) :
    ((m2 * m1) ^ d) 0 1 = 2 * ((m2 * m1) ^ d) 1 0 := by
  have h := congrArg (fun m : Mat => m 0 0)
    (pow_mul_comm (m2 * m1) d 1)
  simp only [pow_one] at h
  norm_num [m1, m2, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  omega

/-- The shorter left block gives the smaller denominator when the numerator ties. -/
theorem blockWord_swap (i d : ℕ) :
    LexLE (convergent (blockWord i (i + d)))
      (convergent (blockWord (i + d) i)) := by
  have hdiag : blockMatrix i (i + d) 0 0 = blockMatrix (i + d) i 0 0 := by
    have h := congrArg (fun m : Mat => m 0 0) (blockMatrix_transpose i (i + d))
    exact h
  have hoff : blockMatrix i (i + d) 0 1 - blockMatrix i (i + d) 1 0 =
      ((m2 * m1) ^ d) 0 1 - ((m2 * m1) ^ d) 1 0 := by
    clear hdiag
    induction i with
    | zero => simp [blockMatrix]
    | succ i ih =>
      rw [show i + 1 + d = (i + d) + 1 by omega, blockMatrix_succ,
        sandwich_off_diagonal]
      exact ih
  have hswap : blockMatrix i (i + d) 0 1 = blockMatrix (i + d) i 1 0 := by
    exact congrArg (fun m : Mat => m 1 0) (blockMatrix_transpose i (i + d))
  rw [alternating_off_diagonal] at hoff
  have hn := alternating_nonneg d
  rw [hswap, (blockMatrix_column _ _).2, (blockMatrix_column _ _).2] at hoff
  rw [(blockMatrix_column _ _).1, (blockMatrix_column _ _).1] at hdiag
  right
  constructor <;> omega

/-- A gap of at least two blocks makes the numerator strictly too large. -/
theorem blockWord_balance_step (i d : ℕ) :
    (convergent (blockWord (i + 1) (i + d + 1))).1 <
      (convergent (blockWord i (i + d + 2))).1 := by
  have h := congrArg (fun m : Mat => m 0 0) (blockMatrix_exchange i (d + 1))
  have hp := alternating_positive d
  simp only [Matrix.sub_apply] at h
  have he : ((m2 * m1 - m1 * m2) * (m2 * m1) ^ (d + 1)) 0 0 =
      ((m2 * m1) ^ (d + 1)) 1 0 := by
    norm_num [m1, m2, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, (blockMatrix_column _ _).1, (blockMatrix_column _ _).1] at h
  convert (show (convergent (blockWord (i + 1) (i + (d + 1)))).1 <
    (convergent (blockWord i (i + (d + 1) + 1))).1 by omega) using 1

private theorem blockWord_balanced_ordered (i d : ℕ) :
    LexLE (candidate (2 * (2 * i + d))) (convergent (blockWord i (i + d))) := by
  induction d using Nat.strong_induction_on generalizing i with
  | h d ih =>
    rcases d with _ | d
    · have hc : candidateWord (2 * (2 * i + 0)) = blockWord i (i + 0) := by
        simp [candidateWord, blockWord, show 2 * (2 * i) = 4 * i by omega, Nat.mul_mod]
      right
      simp only [candidate, hc]
      exact ⟨trivial, le_rfl⟩
    · rcases d with _ | d
      · have hc : candidateWord (2 * (2 * i + 1)) = blockWord i (i + 1) := by
          simp [candidateWord, blockWord, show 2 * (2 * i + 1) = 4 * i + 2 by omega,
            Nat.add_div, Nat.add_mod, Nat.mul_mod]
        right
        simp only [candidate, hc]
        exact ⟨trivial, le_rfl⟩
      · have hi := ih d (by omega) (i + 1)
        have hc : 2 * (2 * (i + 1) + d) = 2 * (2 * i + (d + 1 + 1)) := by omega
        rw [hc] at hi
        have hb := blockWord_balance_step i d
        have he : i + 1 + d = i + d + 1 := by omega
        rw [he] at hi
        have he'' : i + (d + 1 + 1) = i + d + 2 := by omega
        rw [he'']
        left
        rcases hi with hi | ⟨hi, _⟩ <;> omega

/-- For a fixed total number of alternating blocks, the paper's candidate
    is minimal, including the denominator tie-break when the total is odd. -/
theorem blockWord_balanced (i j : ℕ) :
    LexLE (candidate (2 * (i + j))) (convergent (repeat12 i ++ repeat21 j)) := by
  rcases le_total i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb := blockWord_balanced_ordered i d
    simpa [blockWord, show 2 * i + d = i + (i + d) by omega] using hb
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb := blockWord_balanced_ordered j d
    have hs := blockWord_swap j d
    have he : 2 * j + d = j + d + j := by omega
    rw [he] at hb
    change LexLE (candidate (2 * (j + d + j))) (convergent (blockWord (j + d) j))
    unfold LexLE at *
    omega

theorem blockWord_numerator_swap (i j : ℕ) :
    (convergent (blockWord i j)).1 = (convergent (blockWord j i)).1 := by
  have h := congrArg (fun m : Mat => m 0 0) (blockMatrix_transpose i j)
  change blockMatrix i j 0 0 = blockMatrix j i 0 0 at h
  rw [(blockMatrix_column _ _).1, (blockMatrix_column _ _).1] at h
  exact_mod_cast h

/-- An unbalanced split cannot minimize the numerator. -/
theorem blockWord_unbalanced_strict (i d : ℕ) :
    (candidate (2 * (2 * i + d + 2))).1 <
      (convergent (blockWord i (i + d + 2))).1 := by
  have hb := blockWord_balanced (i + 1) (i + d + 1)
  have hs := blockWord_balance_step i d
  have he : 2 * (i + 1 + (i + d + 1)) = 2 * (2 * i + d + 2) := by omega
  rw [he] at hb
  change LexLE (candidate (2 * (2 * i + d + 2)))
    (convergent (blockWord (i + 1) (i + d + 1))) at hb
  rcases hb with hb | ⟨hb, _⟩ <;> omega

/-- The even numerator ties occur exactly at the balanced splits. -/
theorem blockWord_numerator_eq_iff (i j : ℕ) :
    (candidate (2 * (i + j))).1 = (convergent (blockWord i j)).1 ↔
      i ≤ j + 1 ∧ j ≤ i + 1 := by
  constructor
  · intro h
    by_contra hn
    have hu : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
    rcases hu with hu | hu
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hu
      have hs := blockWord_unbalanced_strict i d
      have hj : j = i + d + 2 := by omega
      have ht : 2 * (i + j) = 2 * (2 * i + d + 2) := by omega
      rw [ht, hj] at h
      omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hu
      have hs := blockWord_unbalanced_strict j d
      have hi : i = j + d + 2 := by omega
      have ht : 2 * (i + j) = 2 * (2 * j + d + 2) := by omega
      rw [ht, blockWord_numerator_swap i j, hi] at h
      omega
  · intro h
    have hc : i = j ∨ j = i + 1 ∨ i = j + 1 := by omega
    rcases hc with hc | hc | hc
    · subst j
      simp [candidate, candidateWord, blockWord,
        show 2 * (i + i) = 4 * i by omega, Nat.mul_mod]
    · subst j
      simp [candidate, candidateWord, blockWord,
        show 2 * (i + (i + 1)) = 4 * i + 2 by omega,
        Nat.mul_mod, Nat.add_mod, Nat.add_div]
    · subst i
      rw [blockWord_numerator_swap]
      simp [candidate, candidateWord, blockWord,
        show 2 * (j + 1 + j) = 4 * j + 2 by omega,
        Nat.mul_mod, Nat.add_mod, Nat.add_div]

end Lsbgcd
