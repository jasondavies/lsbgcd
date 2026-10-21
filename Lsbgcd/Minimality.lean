module

public import Lsbgcd.Frontier
public import Lsbgcd.Balancing
public import Lsbgcd.Reduction
public import Lsbgcd.ClosedForms

@[expose] public section

/-!
# Global minimality and Theorem 1.1

The proof of binary-continuant minimality uses the domination family from
Frontier and the exact matrix exchange identity from Balancing. It is a
direct proof of the special extremal result needed here, and makes no
assumption about the general permutation theorem quoted from Ramharter.
-/
namespace Lsbgcd

/-- Lexicographic minimality among all admissible words. -/
theorem admissible_minimality : AdmissibleMinimality := by
  intro as ha
  rcases admissible_frontier as ha with ⟨k, hlen, hs⟩ | ⟨i, j, hlen, hs⟩
  · rw [hlen, candidate_odd_word]
    exact smaller_lex hs
  · rw [hlen]
    exact lexLE_trans (blockWord_balanced i j) (smaller_lex hs)

/-- The candidates are the lexicographically least actual inputs: every input
reduces to an admissible word of the same length (`reduction_to_admissible`),
which the candidate word of that length dominates (`admissible_minimality`). -/
theorem candidate_minimality : CandidateMinimality := by
  intro n
  refine ⟨(candidate_positive_ordered n).1, (candidate_positive_ordered n).2,
    candidate_iterations n, ?_⟩
  intro u v hu hv hn
  obtain ⟨as, ha, hlen, hle⟩ := reduction_to_admissible u v hu hv
  have hm := admissible_minimality as ha
  rw [hlen, hn] at hm
  exact lexLE_trans hm hle

/-- Theorem 1.1, including minimality, the order-16 recurrence, and all
six closed forms, with no outstanding hypotheses. -/
theorem theorem1_1 : MainTheorem :=
  ⟨candidate_minimality, candidate_x_order16, candidate_y_order16, candidate_closed_forms⟩

/-- The least input is unique, so the construction agrees with the
paper's description of `(x_n,y_n)` by its minimising property. -/
theorem isWorstCase_iff (n : ℕ) (p : ℕ × ℕ) :
    IsWorstCase n p ↔ p = candidate n := by
  constructor
  · intro hp
    have hc := candidate_minimality n
    have hpc := hp.2.2.2 (candidate n).1 (candidate n).2 hc.1 hc.2.1 hc.2.2.1
    have hcp := hc.2.2.2 p.1 p.2 hp.1 hp.2.1 hp.2.2.1
    apply Prod.ext <;> unfold LexLE at hpc hcp <;> omega
  · rintro rfl
    exact candidate_minimality n

theorem candidate_numerator_le {as : List ℕ} (ha : Admissible as) :
    (candidate as.length).1 ≤ continuant as := by
  have h := admissible_minimality as ha
  rcases h with h | ⟨h, _⟩ <;> unfold continuant <;> omega

private theorem candidate_offset_wordMatrix (n : ℕ) :
    wordMatrix (candidateWord (4 * n + 2)) = offsetMatrix n := by
  rw [candidateWord_four_mul_add_two, blockWord_matrix, offsetMatrix_powers]
  rfl

/-- The two descriptions in Theorem 5.2 are distinct exactly for lengths
congruent to two modulo four. -/
theorem candidateWord_reverse_eq_iff (n : ℕ) :
    (candidateWord n).reverse = candidateWord n ↔ n % 4 ≠ 2 := by
  constructor
  · intro h hn
    have he : n = 4 * (n / 4) + 2 := by omega
    rw [he] at h
    have hm := congrArg wordMatrix h
    rw [wordMatrix_reverse, candidate_offset_wordMatrix] at hm
    have hoff := congrArg (fun m : Mat => m 1 0) hm
    have hd := offset_off_diagonal (n / 4)
    simp only [Matrix.transpose_apply] at hoff
    omega
  · intro hn
    unfold candidateWord
    split_ifs with ho he
    · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, repeat12_reverse]
      exact (repeat12_one _).symm
    · exact blockWord_reverse _ _
    · omega

/-- Equality characterisation of the minimal continuant in Theorem 5.2.
Reversal is the only possible alternative; for the palindromic cases it
is the same word. -/
theorem minimal_continuant_eq_iff (as : List ℕ) (ha : Admissible as) :
    continuant as = (candidate as.length).1 ↔
      as = candidateWord as.length ∨ as = (candidateWord as.length).reverse := by
  constructor
  · intro he
    rcases admissible_frontier_eq as ha with ⟨k, hlen, hs, hw⟩ | ⟨i, j, hlen, hs, hw⟩
    · left
      have hc : candidateWord as.length = repeat12 k ++ [1] := by
        rw [hlen, candidateWord_two_mul_add_one]
      rw [hc]
      apply hw
      simpa only [continuant, candidate, hc] using he.symm
    · have hb := blockWord_balanced i j
      have hnum : (candidate (2 * (i + j))).1 ≤
          (convergent (blockWord i j)).1 := by
        rcases hb with hb | ⟨hb, _⟩ <;> omega
      have he' : (convergent (blockWord i j)).1 = (convergent as).1 := by
        rw [hlen] at he
        unfold continuant at he
        have hs' := hs.1
        omega
      have has := hw he'
      have heq : (candidate (2 * (i + j))).1 = (convergent (blockWord i j)).1 := by
        rw [hlen] at he
        unfold continuant at he
        simpa only [blockWord] using he.symm.trans he'.symm
      have hbal := (blockWord_numerator_eq_iff i j).1 heq
      have hc : i = j ∨ j = i + 1 ∨ i = j + 1 := by omega
      rcases hc with hc | hc | hc
      · subst j
        left
        rw [hlen, has, show 2 * (i + i) = 4 * i by omega, candidateWord_four_mul]
      · subst j
        left
        rw [hlen, has, show 2 * (i + (i + 1)) = 4 * i + 2 by omega,
          candidateWord_four_mul_add_two]
      · subst i
        right
        rw [hlen, has, show 2 * (j + 1 + j) = 4 * j + 2 by omega,
          candidateWord_four_mul_add_two, blockWord_reverse]
  · rintro (h | h)
    · change continuant as = continuant (candidateWord as.length)
      rw [← h]
    · change continuant as = continuant (candidateWord as.length)
      calc
        continuant as = continuant ((candidateWord as.length).reverse) := congrArg continuant h
        _ = _ := continuant_reverse _

/-- Theorem 5.2 as a minimisation statement over all admissible words of
the same length, with exactly the stated minimisers up to reversal. -/
theorem theorem5_2 (as : List ℕ) (ha : Admissible as) :
    (∀ bs : List ℕ, Admissible bs → bs.length = as.length →
      continuant as ≤ continuant bs) ↔
    as = candidateWord as.length ∨ as = (candidateWord as.length).reverse := by
  rw [← minimal_continuant_eq_iff as ha]
  constructor
  · intro h
    have hu := h (candidateWord as.length) (candidateWord_admissible _) (candidateWord_length _)
    have hl := candidate_numerator_le ha
    change continuant as ≤ (candidate as.length).1 at hu
    omega
  · intro he bs hb hlen
    rw [he, ← hlen]
    exact candidate_numerator_le hb

end Lsbgcd
