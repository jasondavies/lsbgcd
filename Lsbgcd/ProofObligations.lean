module

public import Lsbgcd.ClosedForms

@[expose] public section

/-! # Splitting global minimality into reduction and continuant minimisation -/
namespace Lsbgcd

theorem lexLE_trans {p q r : ℕ × ℕ} (hpq : LexLE p q) (hqr : LexLE q r) :
    LexLE p r := by
  unfold LexLE at *
  omega

/-- Reduction.lean and Minimality.lean discharge these two hypotheses;
their combination gives the unconditional `candidate_minimality`. -/
theorem minimality_of_reduction (reduction : ReductionToAdmissible)
    (minimality : AdmissibleMinimality) : CandidateMinimality := by
  intro n
  refine ⟨(candidate_positive_ordered n).1, (candidate_positive_ordered n).2,
    candidate_iterations n, ?_⟩
  intro u v hu hv hn
  obtain ⟨as, ha, hlen, hle⟩ := reduction u v hu hv
  have hm := minimality as ha
  rw [hlen, hn] at hm
  exact lexLE_trans hm hle

/-- Combining reduction and continuant minimisation completes Theorem 1.1. -/
theorem main_of_reduction_and_minimality (reduction : ReductionToAdmissible)
    (minimality : AdmissibleMinimality) : MainTheorem :=
  main_of_minimality (minimality_of_reduction reduction minimality)

end Lsbgcd
