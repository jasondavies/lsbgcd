import Lsbgcd.RamharterFinite
import Lsbgcd.RamharterWeighted
import Lsbgcd.RamharterShape

/-! # Logical steps for the alternating permutation-minimum induction -/
namespace Lsbgcd

/-- The two possible words, with reversal permitted only at symmetric boundaries. -/
def RamharterNormalForm (l r : ℚ) (bs cs : List ℕ) : Prop :=
  cs = ramharterWord bs ∨ l = r ∧ cs = (ramharterWord bs).reverse

theorem isCostMinimum_perm {cost : List ℕ → ℚ} {bs cs ds : List ℕ}
    (h : IsCostMinimum cost bs cs) (hp : bs.Perm ds) :
    IsCostMinimum cost ds cs :=
  ⟨h.1.trans hp, fun xs hx => h.2 xs (hx.trans hp.symm)⟩

theorem weighted_minimum_reverse {l r : ℚ} {bs cs : List ℕ}
    (he : l = r) (h : IsCostMinimum (weightedContinuant l r) bs cs) :
    IsCostMinimum (weightedContinuant l r) bs cs.reverse := by
  refine ⟨(List.reverse_perm cs).trans h.1, ?_⟩
  intro ds hd
  simpa only [weightedContinuant_reverse, he] using h.2 ds hd

/-- A minimum with fixed endpoints induces an interior minimum. -/
theorem weighted_minimum_peel {l r : ℚ} {a b : ℕ} {rest mid : List ℕ}
    (hl : 0 ≤ l) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hp : mid.Perm rest)
    (h : IsCostMinimum (weightedContinuant l r) (a :: b :: rest)
      (a :: (mid ++ [b]))) :
    IsCostMinimum (weightedContinuant (1 / ((a : ℚ) + l))
      (1 / ((b : ℚ) + r))) rest.reverse mid := by
  refine ⟨hp.trans (List.reverse_perm rest).symm, ?_⟩
  intro ds hd
  apply (weightedContinuant_peel_le_iff mid ds hl hr ha hb).mp
  apply h.2
  have hp' : ds.Perm rest := hd.trans (List.reverse_perm rest)
  exact (List.Perm.cons a (hp'.append_right [b])).trans
    (List.Perm.cons a (List.perm_append_comm (l₁ := rest) (l₂ := [b])))

/-- The only interior reversal case lifts to whole-word reversal because
coincident updated boundaries force coincident endpoint digits. -/
theorem ramharterNormalForm_peel {l r : ℚ} {a b : ℕ} {rest mid : List ℕ}
    (he : 1 / ((a : ℚ) + l) = 1 / ((b : ℚ) + r) → a = b ∧ l = r)
    (h : RamharterNormalForm (1 / ((a : ℚ) + l))
      (1 / ((b : ℚ) + r)) rest.reverse mid) :
    RamharterNormalForm l r (a :: b :: rest) (a :: (mid ++ [b])) := by
  rcases h with h | ⟨heq, h⟩
  · left
    rw [ramharterWord_two, h]
  · obtain ⟨hab, hlr⟩ := he heq
    right
    refine ⟨hlr, ?_⟩
    rw [ramharterWord_two, h]
    simp [List.reverse_append, hab]

theorem ramharterNormalForm_of_reverse {l r : ℚ} {bs cs : List ℕ}
    (he : l = r) (h : RamharterNormalForm l r bs cs.reverse) :
    RamharterNormalForm l r bs cs := by
  rcases h with h | ⟨_, h⟩
  · exact Or.inr ⟨he, by simpa using congrArg List.reverse h⟩
  · exact Or.inl (by simpa using congrArg List.reverse h)

/-- Classifying all attained minima proves that the designated word is itself
a minimum. Finiteness supplies attainment; boundary symmetry equates its reverse. -/
theorem weighted_minimum_of_normalForms {l r : ℚ} {bs : List ℕ}
    (hclass : ∀ cs, IsCostMinimum (weightedContinuant l r) bs cs →
      RamharterNormalForm l r bs cs) :
    IsCostMinimum (weightedContinuant l r) bs (ramharterWord bs) := by
  obtain ⟨cs, hc⟩ := exists_cost_minimum (weightedContinuant l r) bs
  refine ⟨ramharterWord_perm bs, ?_⟩
  intro ds hd
  rcases hclass cs hc with h | ⟨he, h⟩
  · simpa only [h] using hc.2 ds hd
  · simpa only [h, weightedContinuant_reverse, he] using hc.2 ds hd

end Lsbgcd
