module

public import Lsbgcd.Ramharter
public import Lsbgcd.ContinuantOrder

@[expose] public section

/-! # Necessary endpoint conditions for the general permutation minimum -/
namespace Lsbgcd

/-- A suffix with increasing endpoints can be reversed to decrease the
continuant whenever a nonempty prefix precedes it. -/
theorem continuant_suffix_reverse_lt (pre mid : List ℕ) (x y : ℕ)
    (hpre : ∀ a ∈ pre, 0 < a) (hne : pre ≠ [])
    (hmid : ∀ a ∈ mid, 0 < a) (hxy : x < y) :
    continuant (pre ++ (x :: (mid ++ [y])).reverse) <
      continuant (pre ++ (x :: (mid ++ [y]))) := by
  have hs := wordMatrix_endpoints_strict hmid hxy
  have hp := wordMatrix_upper_right_positive hpre hne
  have hd := continuant_reverse_interval_difference pre (x :: (mid ++ [y])) []
  have h0 : wordMatrix [] 1 0 = 0 := rfl
  have h1 : wordMatrix [] 0 0 = 1 := rfl
  simp only [List.append_nil, h0, h1, mul_zero, mul_one, zero_sub] at hd
  have hm : 0 < (wordMatrix (x :: (mid ++ [y])) 1 0 -
      wordMatrix (x :: (mid ++ [y])) 0 1) * wordMatrix pre 0 1 :=
    mul_pos (sub_pos.mpr hs) hp
  nlinarith

/-- In a minimum arrangement, each interior digit is at least the last
one. This works for every positive multiset, with no binary restriction. -/
theorem permutation_minimum_last_le_interior {bs : List ℕ} {a b : ℕ} {mid : List ℕ}
    (hpos : ∀ x ∈ a :: (mid ++ [b]), 0 < x)
    (hmin : IsPermutationMinimum bs (a :: (mid ++ [b]))) :
    ∀ x ∈ mid, b ≤ x := by
  intro x hx
  by_contra hn
  have hxb : x < b := by omega
  obtain ⟨left, right, hm⟩ := List.mem_iff_append.mp hx
  have hp : ∀ z ∈ a :: left, 0 < z := by
    intro z hz
    apply hpos z
    simp only [List.mem_cons] at hz ⊢
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · right
      rw [hm]
      simp only [List.mem_append, List.mem_cons]
      exact Or.inl (Or.inl hz)
  have hr : ∀ z ∈ right, 0 < z := by
    intro z hz
    apply hpos z
    rw [hm]
    simp only [List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inr (Or.inr hz)))
  have he : a :: (mid ++ [b]) = (a :: left) ++ (x :: (right ++ [b])) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc]
  have hs := continuant_suffix_reverse_lt (a :: left) right x b hp (by simp) hr hxb
  have hperm : ((a :: left) ++ (x :: (right ++ [b])).reverse).Perm bs := by
    apply List.Perm.trans ((List.Perm.refl (a :: left)).append (List.reverse_perm _))
    rw [← he]
    exact hmin.1
  have hle := hmin.2 _ hperm
  rw [he] at hle
  omega

/-- Reversing a globally minimizing arrangement preserves global minimality. -/
theorem permutation_minimum_reverse {bs cs : List ℕ}
    (h : IsPermutationMinimum bs cs) : IsPermutationMinimum bs cs.reverse := by
  refine ⟨(List.reverse_perm cs).trans h.1, ?_⟩
  intro as hp
  simpa only [continuant_reverse] using h.2 as hp

/-- Both endpoints of a minimizing arrangement are no greater than every
interior digit. Orienting the endpoints increasingly therefore puts the two
smallest entries at the ends, with multiplicity respected. -/
theorem permutation_minimum_endpoints {bs : List ℕ} {a b : ℕ} {mid : List ℕ}
    (hpos : ∀ x ∈ a :: (mid ++ [b]), 0 < x)
    (hmin : IsPermutationMinimum bs (a :: (mid ++ [b]))) :
    ∀ x ∈ mid, a ≤ x ∧ b ≤ x := by
  have hr : (a :: (mid ++ [b])).reverse = b :: (mid.reverse ++ [a]) := by simp
  have hp : ∀ x ∈ b :: (mid.reverse ++ [a]), 0 < x := by
    intro x hx
    apply hpos x
    rw [← List.mem_reverse, hr]
    exact hx
  have hm := permutation_minimum_reverse hmin
  rw [hr] at hm
  have hfirst := permutation_minimum_last_le_interior hp hm
  have hlast := permutation_minimum_last_le_interior hpos hmin
  intro x hx
  exact ⟨hfirst x (by simpa using hx), hlast x hx⟩

/-- A positive word of length at least two has a continued-fraction value
strictly greater than any lower bound on its digits. -/
theorem wordMatrix_lower_bound_strict {as : List ℕ} (a : ℕ)
    (hpos : ∀ x ∈ as, 0 < x) (hbound : a ≤ as.headD 0)
    (hlen : 2 ≤ as.length) :
    (a : ℤ) * wordMatrix as 1 0 < wordMatrix as 0 0 := by
  cases as with
  | nil => simp at hlen
  | cons b bs =>
    have hb : a ≤ b := by simpa using hbound
    have hp : ∀ x ∈ bs, 0 < x := fun x hx => hpos x (by simp [hx])
    have hn : bs ≠ [] := by intro he; simp [he] at hlen
    have hd := positive_convergent_denominator hp hn
    rw [(wordMatrix_first_column _).1, (wordMatrix_first_column _).2]
    simp only [convergent, Nat.cast_add, Nat.cast_mul]
    have hb' : (a : ℤ) ≤ b := by exact_mod_cast hb
    have hq : (0 : ℤ) < (convergent bs).2 := by exact_mod_cast hd
    have hr : (0 : ℤ) ≤ (convergent bs).1 := by positivity
    nlinarith

/-- Once the smallest digits occupy the ends, a larger interior digit can
be moved toward the left end by a strictly decreasing interval reversal. -/
theorem continuant_inner_reverse_lt (a x z : ℕ) (mid suf : List ℕ)
    (hm : ∀ t ∈ mid, 0 < t) (hs : ∀ t ∈ suf, 0 < t)
    (hb : a ≤ suf.headD 0) (hlen : 2 ≤ suf.length) (hxz : x < z) :
    continuant ([a] ++ (x :: (mid ++ [z])).reverse ++ suf) <
      continuant ([a] ++ (x :: (mid ++ [z])) ++ suf) := by
  have hk := wordMatrix_endpoints_strict hm hxz
  have hd := continuant_reverse_interval_difference [a] (x :: (mid ++ [z])) suf
  have hb' := wordMatrix_lower_bound_strict a hs hb hlen
  have h00 : wordMatrix [a] 0 0 = a := by simp [wordMatrix, digitMatrix]
  have h01 : wordMatrix [a] 0 1 = 1 := by simp [wordMatrix, digitMatrix]
  rw [h00, h01, one_mul] at hd
  have hprod : 0 <
      (wordMatrix (x :: (mid ++ [z])) 1 0 - wordMatrix (x :: (mid ++ [z])) 0 1) *
        (wordMatrix suf 0 0 - (a : ℤ) * wordMatrix suf 1 0) :=
    mul_pos (sub_pos.mpr hk) (sub_pos.mpr hb')
  nlinarith

/-- The second digit of a minimum is at least every digit strictly between
its second and penultimate positions. -/
theorem permutation_minimum_second_ge_middle {bs : List ℕ} {a b x y : ℕ}
    {mid : List ℕ} (hpos : ∀ t ∈ a :: x :: (mid ++ [y,b]), 0 < t)
    (hmin : IsPermutationMinimum bs (a :: x :: (mid ++ [y,b]))) :
    ∀ z ∈ mid, z ≤ x := by
  intro z hz
  by_contra hn
  have hxz : x < z := by omega
  obtain ⟨left, right, hm⟩ := List.mem_iff_append.mp hz
  have he : a :: x :: (mid ++ [y,b]) =
      [a] ++ (x :: (left ++ [z])) ++ (right ++ [y,b]) := by
    rw [hm]
    simp [List.append_assoc]
  have hml : ∀ t ∈ left, 0 < t := by
    intro t ht
    apply hpos t
    rw [hm]
    simp only [List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (Or.inl ht)))
  have hsr : ∀ t ∈ right ++ [y,b], 0 < t := by
    intro t ht
    apply hpos t
    rw [he]
    simp only [List.mem_append]
    exact Or.inr (List.mem_append.mp ht)
  have hbound : a ≤ (right ++ [y,b]).headD 0 := by
    have ha : ∀ t ∈ x :: (mid ++ [y]), a ≤ t ∧ b ≤ t := by
      apply permutation_minimum_endpoints
      · simpa [List.append_assoc] using hpos
      · simpa [List.append_assoc] using hmin
    cases right with
    | nil => simpa using (ha y (by simp)).1
    | cons t ts =>
      have ht := (ha t (by simp [hm])).1
      simpa using ht
  have hs := continuant_inner_reverse_lt a x z left (right ++ [y,b]) hml hsr
    hbound (by simp) hxz
  have hp : ([a] ++ (x :: (left ++ [z])).reverse ++ (right ++ [y,b])).Perm bs := by
    apply List.Perm.trans
      (((List.Perm.refl [a]).append (List.reverse_perm _)).append
        (List.Perm.refl (right ++ [y,b])))
    rw [← he]
    exact hmin.1
  have hu := hmin.2 _ hp
  rw [he] at hu
  omega

/-- The two digits adjacent to the endpoints are the two largest digits
remaining after the endpoints have been removed. -/
theorem permutation_minimum_next_endpoints {bs : List ℕ} {a b x y : ℕ}
    {mid : List ℕ} (hpos : ∀ t ∈ a :: x :: (mid ++ [y,b]), 0 < t)
    (hmin : IsPermutationMinimum bs (a :: x :: (mid ++ [y,b]))) :
    ∀ z ∈ mid, z ≤ x ∧ z ≤ y := by
  have hr : (a :: x :: (mid ++ [y,b])).reverse =
      b :: y :: (mid.reverse ++ [x,a]) := by simp
  have hp : ∀ t ∈ b :: y :: (mid.reverse ++ [x,a]), 0 < t := by
    intro t ht
    apply hpos t
    rw [← List.mem_reverse, hr]
    exact ht
  have hm := permutation_minimum_reverse hmin
  rw [hr] at hm
  have hl := permutation_minimum_second_ge_middle hpos hmin
  have hr' := permutation_minimum_second_ge_middle hp hm
  intro z hz
  exact ⟨hl z hz, hr' z (by simpa using hz)⟩

/-- Distinct endpoints determine the orientation of the two largest digits:
the larger adjacent digit is next to the smaller endpoint. -/
theorem permutation_minimum_opposite_order {bs : List ℕ} {a b x y : ℕ}
    {mid : List ℕ} (hpos : ∀ t ∈ a :: x :: (mid ++ [y,b]), 0 < t)
    (hmin : IsPermutationMinimum bs (a :: x :: (mid ++ [y,b])))
    (hab : a < b) : y ≤ x := by
  by_contra hn
  have hxy : x < y := by omega
  have hm : ∀ t ∈ mid, 0 < t := by
    intro t ht
    exact hpos t (by simp [ht])
  have hs := wordMatrix_endpoints_strict hm hxy
  have hd := continuant_reverse_interval_difference [a] (x :: (mid ++ [y])) [b]
  have h1 : wordMatrix [a] 0 0 = a := by simp [wordMatrix, digitMatrix]
  have h2 : wordMatrix [a] 0 1 = 1 := by simp [wordMatrix, digitMatrix]
  have h3 : wordMatrix [b] 0 0 = b := by simp [wordMatrix, digitMatrix]
  have h4 : wordMatrix [b] 1 0 = 1 := by simp [wordMatrix, digitMatrix]
  rw [h1, h2, h3, h4, mul_one, one_mul] at hd
  have hab' : (a : ℤ) < b := by exact_mod_cast hab
  have hprod : 0 <
      (wordMatrix (x :: (mid ++ [y])) 1 0 - wordMatrix (x :: (mid ++ [y])) 0 1) *
        ((b : ℤ) - a) := mul_pos (sub_pos.mpr hs) (sub_pos.mpr hab')
  have he : [a] ++ (x :: (mid ++ [y])) ++ [b] = a :: x :: (mid ++ [y,b]) := by
    simp [List.append_assoc]
  have hp : ([a] ++ (x :: (mid ++ [y])).reverse ++ [b]).Perm bs := by
    apply List.Perm.trans
      (((List.Perm.refl [a]).append (List.reverse_perm _)).append (List.Perm.refl [b]))
    rw [he]
    exact hmin.1
  have hu := hmin.2 _ hp
  rw [he] at hd
  nlinarith

end Lsbgcd
