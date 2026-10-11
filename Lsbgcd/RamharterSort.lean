import Lsbgcd.RamharterSortingCore
import Lsbgcd.RamharterWeightedExtrema
import Lsbgcd.RamharterOrientation

/-!
# General Ramharter permutation minimum

Strict boundary comparisons force the two next extreme digits to the
endpoints. Peeling them reverses the order on the remaining multiset.
The induction keeps the equality case and therefore proves uniqueness
up to reversal, including repeated digits.
-/
namespace Lsbgcd

/-- Every minimum in an alternating strict boundary context has the
Ramharter arrangement, with reversal possible only for equal boundaries. -/
theorem ramharter_minimum_normalForm {high : Bool} {lo hi : ℕ} {l r : ℚ}
    {bs cs : List ℕ} (H : RamharterContext high lo hi l r) (hlo : 0 < lo)
    (hw : DigitsWithin lo hi bs)
    (hs : bs.Pairwise (fun a b => ramharterKey high a ≤ ramharterKey high b))
    (hmin : IsCostMinimum (weightedContinuant l r) bs cs) :
    RamharterNormalForm l r bs cs := by
  generalize hn : bs.length = n
  induction n using Nat.strong_induction_on generalizing high lo hi l r bs cs with
  | h n ih =>
    cases bs with
    | nil =>
      have he : cs = [] := List.perm_nil.mp hmin.1
      subst cs
      exact Or.inl rfl
    | cons a bs =>
      cases bs with
      | nil =>
        have he : cs = [a] := List.perm_singleton.mp hmin.1
        subst cs
        exact Or.inl (ramharterWord_singleton a).symm
      | cons b rest =>
        have oriented : ∀ x y mid,
            IsCostMinimum (weightedContinuant l r) (a :: b :: rest)
              (x :: (mid ++ [y])) →
            ramharterKey high x ≤ ramharterKey high y →
            RamharterNormalForm l r (a :: b :: rest) (x :: (mid ++ [y])) := by
          intro x y mid hm hxy
          have hwm : DigitsWithin lo hi (x :: (mid ++ [y])) :=
            fun z hz => hw z (hm.1.mem_iff.mp hz)
          have hend := ramharter_weighted_minimum_endpoints H hlo hwm
            (fun ds hd => hm.2 ds (hd.trans hm.1))
          obtain ⟨hxa, hyb, hp⟩ := sorted_endpoints_identify (ramharterKey high)
            (ramharterKey_injective high) hs hm.1 hxy hend
          subst x
          subst y
          obtain ⟨H', hw', hs'⟩ := ramharterContext_step H hlo hw hs
          have ha : 0 < a := hlo.trans_le (hw a (by simp)).1
          have hb : 0 < b := hlo.trans_le (hw b (by simp)).1
          have hlo' : 0 < (if high then lo else b) := by cases high <;> assumption
          have hinner := weighted_minimum_peel H.nonneg_left H.nonneg_right ha hb hp hm
          have hlen : rest.reverse.length < n := by
            simp only [List.length_reverse]
            simp only [List.length_cons] at hn
            omega
          have hi := ih rest.reverse.length hlen H' hlo' hw' hs' hinner rfl
          exact ramharterNormalForm_peel (ramharterContext_update_eq_iff H hxy).mp hi
        have hlen : 2 ≤ cs.length := by rw [hmin.1.length_eq]; simp
        obtain ⟨x, y, mid, rfl⟩ := list_outer_decomposition cs hlen
        have hwm : DigitsWithin lo hi (x :: (mid ++ [y])) :=
          fun z hz => hw z (hmin.1.mem_iff.mp hz)
        have hmid : ∀ z ∈ mid, 0 < z := by
          intro z hz
          exact hlo.trans_le (hwm z (by simp [hz])).1
        by_cases hxy : ramharterKey high x ≤ ramharterKey high y
        · exact oriented x y mid hmin hxy
        · have he : l = r :=
            (ramharter_weighted_endpoint_order H hmid
              (hmin.2 _ ((List.reverse_perm _).trans hmin.1))).resolve_left hxy
          apply ramharterNormalForm_of_reverse he
          have hrev := weighted_minimum_reverse he hmin
          have heq : (x :: (mid ++ [y])).reverse = y :: (mid.reverse ++ [x]) := by simp
          rw [heq] at hrev ⊢
          exact oriented y x mid.reverse hrev (le_of_lt (lt_of_not_ge hxy))

/-- Theorem 5.1: for every sorted positive multiset, Ramharter's arrangement
minimises the continuant, and these are its only minimising digit words
up to reversal. The statement also covers the empty and singleton cases. -/
theorem ramharter_theorem : RamharterTheorem := by
  intro bs hpos hs
  have hw : DigitsWithin 1 bs.sum bs := by
    intro b hb
    exact ⟨hpos b hb, List.le_sum_of_mem hb⟩
  have H : RamharterContext false 1 bs.sum 0 0 := lowBoundaryContext_zero (by norm_num)
  have hs' : bs.Pairwise (fun a b => ramharterKey false a ≤ ramharterKey false b) := by
    simpa [ramharterKey] using hs
  have hclass : ∀ cs, IsCostMinimum (weightedContinuant 0 0) bs cs →
      RamharterNormalForm 0 0 bs cs :=
    fun cs hmin => ramharter_minimum_normalForm H (by norm_num) hw hs' hmin
  have hmin := weighted_minimum_of_normalForms hclass
  constructor
  · refine ⟨hmin.1, ?_⟩
    intro ds hd
    have hh := hmin.2 ds hd
    simp only [weightedContinuant_zero] at hh
    exact_mod_cast hh
  · intro cs hp
    constructor
    · intro he
      have hc : IsCostMinimum (weightedContinuant 0 0) bs cs := by
        refine ⟨hp, ?_⟩
        intro ds hd
        simpa only [weightedContinuant_zero, he] using hmin.2 ds hd
      rcases hclass cs hc with h | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · rfl
      · exact continuant_reverse _

end Lsbgcd
