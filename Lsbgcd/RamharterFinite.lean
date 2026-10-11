import Lsbgcd.Ramharter

/-! # Finite minimization and the outer-digit step for Ramharter sorting -/
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

end Lsbgcd
