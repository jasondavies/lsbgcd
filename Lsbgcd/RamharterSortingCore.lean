module

public import Lsbgcd.RamharterWeighted
public import Lsbgcd.RamharterShape

@[expose] public section

/-!
# Logical steps for the alternating permutation-minimum induction

This module holds the parts of the induction in `RamharterSort.lean` that do
not depend on the continuant inequalities: attainment of a minimum over a
finite permutation class, the decomposition of a word into endpoints and
interior, identification of the endpoints of a sorted multiset, and the
bookkeeping that lifts a classification of interior minima
(`RamharterNormalForm`) to the whole word.
-/
namespace Lsbgcd

/-- A minimum of an arbitrary rational-valued cost over one permutation class. -/
def IsCostMinimum (cost : List ℕ → ℚ) (bs cs : List ℕ) : Prop :=
  cs.Perm bs ∧ ∀ ds, ds.Perm bs → cost cs ≤ cost ds

theorem exists_cost_minimum (cost : List ℕ → ℚ) (bs : List ℕ) :
    ∃ cs, IsCostMinimum cost bs cs := by
  have hn : bs.permutations.toFinset.Nonempty := by
    refine ⟨bs, ?_⟩
    simp only [List.mem_toFinset, List.mem_permutations]
    exact List.Perm.refl _
  obtain ⟨cs, hcs, hle⟩ := Finset.exists_min_image bs.permutations.toFinset cost hn
  refine ⟨cs, ?_, ?_⟩
  · simpa only [List.mem_toFinset, List.mem_permutations] using hcs
  · intro ds hp
    exact hle ds (by simpa only [List.mem_toFinset, List.mem_permutations] using hp)

/-- Every list with at least two digits has two endpoints and an interior. -/
theorem list_outer_decomposition (xs : List ℕ) (h : 2 ≤ xs.length) :
    ∃ a b mid, xs = a :: (mid ++ [b]) := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases he : xs.reverse with
    | nil =>
      have hx : xs = [] := by simpa using congrArg List.reverse he
      simp [hx] at h
    | cons b rest =>
      refine ⟨a, b, rest.reverse, ?_⟩
      have hx := congrArg List.reverse he
      simpa using congrArg (List.cons a) hx

/-- If both endpoint keys are below all interior keys, their order fixes
which two entries of the sorted multiset they are. This is independent of
the continuant cost and works for ascending or descending digit keys. -/
theorem sorted_endpoints_identify (key : ℕ → ℤ) (hinj : Function.Injective key)
    {a b x y : ℕ} {rest mid : List ℕ}
    (hs : (a :: b :: rest).Pairwise (fun u v => key u ≤ key v))
    (hp : (x :: (mid ++ [y])).Perm (a :: b :: rest))
    (hxy : key x ≤ key y)
    (hend : ∀ z ∈ mid, key x ≤ key z ∧ key y ≤ key z) :
    x = a ∧ y = b ∧ mid.Perm rest := by
  have ha := (List.pairwise_cons.mp hs).1
  have hb := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hax : key a ≤ key x := by
    have hx : x ∈ a :: b :: rest := hp.mem_iff.mp (by simp)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact ha x hx
  have hxa : key x ≤ key a := by
    have hx : a ∈ x :: (mid ++ [y]) := hp.mem_iff.mpr (by simp)
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact le_rfl
    · exact (hend a hx).1
    · exact hxy
  have he : x = a := hinj (le_antisymm hxa hax)
  subst x
  have htail := hp.cons_inv
  have hby : key b ≤ key y := by
    have hy : y ∈ b :: rest := htail.mem_iff.mp (by simp)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_rfl
    · exact hb y hy
  have hyb : key y ≤ key b := by
    have hy : b ∈ mid ++ [y] := htail.mem_iff.mpr (by simp)
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact (hend b hy).2
    · exact le_rfl
  have he : y = b := hinj (le_antisymm hyb hby)
  subst y
  refine ⟨rfl, rfl, ?_⟩
  have he : (b :: mid).Perm (mid ++ [b]) := by
    exact List.perm_append_comm (l₁ := [b]) (l₂ := mid)
  exact (he.trans htail).cons_inv

/-- The conclusion of the induction for a weighted minimum `cs` of the
multiset `bs`: `cs` is Ramharter's arrangement of `bs`, or, only when the two
boundary values are equal, its reverse. -/
def RamharterNormalForm (l r : ℚ) (bs cs : List ℕ) : Prop :=
  cs = ramharterWord bs ∨ l = r ∧ cs = (ramharterWord bs).reverse

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
