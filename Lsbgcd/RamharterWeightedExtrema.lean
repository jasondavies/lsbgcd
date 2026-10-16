module

public import Lsbgcd.RamharterWeighted
public import Lsbgcd.RamharterMatrix
public import Lsbgcd.RamharterMode

@[expose] public section

/-! # Extremal endpoints of weighted permutation minima -/
namespace Lsbgcd

private theorem within_positive {lo hi : ℕ} {as : List ℕ} (hlo : 0 < lo)
    (h : DigitsWithin lo hi as) : ∀ a ∈ as, 0 < a :=
  fun a ha => hlo.trans_le (h a ha).1

private theorem endpoint_skew_pos {as : List ℕ} {x y : ℕ}
    (hpos : ∀ a ∈ as, 0 < a) (hyx : y < x) :
    0 < (wordMatrix (x :: (as ++ [y])) 0 1 : ℚ) -
      (wordMatrix (x :: (as ++ [y])) 1 0 : ℚ) := by
  have hh : ∀ a ∈ as.reverse, 0 < a := by simpa using hpos
  have hs := wordMatrix_endpoints_strict hh hyx
  have he : y :: (as.reverse ++ [x]) = (x :: (as ++ [y])).reverse := by simp
  rw [he, wordMatrix_reverse] at hs
  simp only [Matrix.transpose_apply] at hs
  exact sub_pos.mpr (by exact_mod_cast hs)

private theorem endpoint_skew_neg {as : List ℕ} {x y : ℕ}
    (hpos : ∀ a ∈ as, 0 < a) (hxy : x < y) :
    (wordMatrix (x :: (as ++ [y])) 0 1 : ℚ) -
      (wordMatrix (x :: (as ++ [y])) 1 0 : ℚ) < 0 := by
  exact sub_neg.mpr (by exact_mod_cast wordMatrix_endpoints_strict hpos hxy)

private theorem boundary_factor_positive {as : List ℕ} {l r : ℚ}
    (hpos : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) (h : l < boundaryCF as r) :
    0 < ((wordMatrix as 1 0 : ℚ) + r * (wordMatrix as 1 1 : ℚ)) -
      l * ((wordMatrix as 0 0 : ℚ) + r * (wordMatrix as 0 1 : ℚ)) := by
  have hh := (boundary_matrix_compare hpos hr).1 h
  nlinarith

private theorem boundary_factor_negative {as : List ℕ} {l r : ℚ}
    (hpos : ∀ a ∈ as, 0 < a) (hr : 0 ≤ r) (h : boundaryCF as r < l) :
    ((wordMatrix as 1 0 : ℚ) + r * (wordMatrix as 1 1 : ℚ)) -
      l * ((wordMatrix as 0 0 : ℚ) + r * (wordMatrix as 0 1 : ℚ)) < 0 := by
  rw [boundaryCF_eq_matrix hpos hr] at h
  have hh := (div_lt_iff₀ (boundary_matrix_denominator_pos hpos hr)).1 h
  nlinarith

/-- In a low context, an initial larger digit can be exchanged with a later
smaller digit by strictly decreasing prefix reversal. -/
theorem low_weighted_prefix_reverse_lt {lo hi x y : ℕ} {l r : ℚ}
    (H : LowBoundaryContext lo hi l r) (hlo : 0 < lo)
    (mid suffix : List ℕ) (hmid : ∀ a ∈ mid, 0 < a)
    (hsuffix : DigitsWithin lo hi suffix) (hne : suffix ≠ []) (hyx : y < x) :
    weightedContinuant l r ((x :: (mid ++ [y])).reverse ++ suffix) <
      weightedContinuant l r ((x :: (mid ++ [y])) ++ suffix) := by
  have hs := endpoint_skew_pos hmid hyx
  have hf := boundary_factor_positive (within_positive hlo hsuffix) H.nonneg_right
    (H.envelope suffix hsuffix hne).1
  have hd := weightedContinuant_reverse_prefix_difference l r (x :: (mid ++ [y])) suffix
  have hp := mul_pos hs hf
  linarith

/-- The high-context version exchanges an initial smaller digit with a later
larger digit. -/
theorem high_weighted_prefix_reverse_lt {lo hi x y : ℕ} {l r : ℚ}
    (H : HighBoundaryContext lo hi l r) (hlo : 0 < lo)
    (mid suffix : List ℕ) (hmid : ∀ a ∈ mid, 0 < a)
    (hsuffix : DigitsWithin lo hi suffix) (hne : suffix ≠ []) (hxy : x < y) :
    weightedContinuant l r ((x :: (mid ++ [y])).reverse ++ suffix) <
      weightedContinuant l r ((x :: (mid ++ [y])) ++ suffix) := by
  have hs := endpoint_skew_neg hmid hxy
  have hf := boundary_factor_negative (within_positive hlo hsuffix) H.nonneg_right
    (H.envelope suffix hsuffix hne).1
  have hd := weightedContinuant_reverse_prefix_difference l r (x :: (mid ++ [y])) suffix
  have hp := mul_pos_of_neg_of_neg hs hf
  linarith

/-- The symmetric low-context suffix exchange. -/
theorem low_weighted_suffix_reverse_lt {lo hi x y : ℕ} {l r : ℚ}
    (H : LowBoundaryContext lo hi l r) (hlo : 0 < lo)
    (pre mid : List ℕ) (hmid : ∀ a ∈ mid, 0 < a)
    (hpre : DigitsWithin lo hi pre) (hne : pre ≠ []) (hxy : x < y) :
    weightedContinuant l r (pre ++ (x :: (mid ++ [y])).reverse) <
      weightedContinuant l r (pre ++ (x :: (mid ++ [y]))) := by
  have hrev : DigitsWithin lo hi pre.reverse := by
    intro a ha
    exact hpre a (by simpa using ha)
  have hf := boundary_factor_positive (within_positive hlo hrev) H.nonneg_left
    (H.envelope pre.reverse hrev (by simpa using hne)).2
  rw [wordMatrix_reverse] at hf
  simp only [Matrix.transpose_apply] at hf
  have hneg : r * ((wordMatrix pre 0 0 : ℚ) + l * (wordMatrix pre 1 0 : ℚ)) -
      ((wordMatrix pre 0 1 : ℚ) + l * (wordMatrix pre 1 1 : ℚ)) < 0 := by linarith
  have hs := endpoint_skew_neg hmid hxy
  have hd := weightedContinuant_reverse_suffix_difference l r pre (x :: (mid ++ [y]))
  have hp := mul_pos_of_neg_of_neg hs hneg
  linarith

/-- The symmetric high-context suffix exchange. -/
theorem high_weighted_suffix_reverse_lt {lo hi x y : ℕ} {l r : ℚ}
    (H : HighBoundaryContext lo hi l r) (hlo : 0 < lo)
    (pre mid : List ℕ) (hmid : ∀ a ∈ mid, 0 < a)
    (hpre : DigitsWithin lo hi pre) (hne : pre ≠ []) (hyx : y < x) :
    weightedContinuant l r (pre ++ (x :: (mid ++ [y])).reverse) <
      weightedContinuant l r (pre ++ (x :: (mid ++ [y]))) := by
  have hrev : DigitsWithin lo hi pre.reverse := by
    intro a ha
    exact hpre a (by simpa using ha)
  have hf := boundary_factor_negative (within_positive hlo hrev) H.nonneg_left
    (H.envelope pre.reverse hrev (by simpa using hne)).2
  rw [wordMatrix_reverse] at hf
  simp only [Matrix.transpose_apply] at hf
  have hpos : 0 < r * ((wordMatrix pre 0 0 : ℚ) + l * (wordMatrix pre 1 0 : ℚ)) -
      ((wordMatrix pre 0 1 : ℚ) + l * (wordMatrix pre 1 1 : ℚ)) := by linarith
  have hs := endpoint_skew_pos hmid hyx
  have hd := weightedContinuant_reverse_suffix_difference l r pre (x :: (mid ++ [y]))
  have hp := mul_pos hs hpos
  linarith

/-- Both endpoints of a weighted minimum in a low context are no greater
than every interior digit. -/
theorem low_weighted_minimum_endpoints {lo hi a b : ℕ} {l r : ℚ} {mid : List ℕ}
    (H : LowBoundaryContext lo hi l r) (hlo : 0 < lo)
    (hw : DigitsWithin lo hi (a :: (mid ++ [b])))
    (hmin : ∀ ds, ds.Perm (a :: (mid ++ [b])) →
      weightedContinuant l r (a :: (mid ++ [b])) ≤ weightedContinuant l r ds) :
    ∀ x ∈ mid, a ≤ x ∧ b ≤ x := by
  intro x hx
  obtain ⟨left, right, hm⟩ := List.mem_iff_append.mp hx
  have hepre : a :: (mid ++ [b]) = (a :: (left ++ [x])) ++ (right ++ [b]) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hesuf : a :: (mid ++ [b]) = (a :: left) ++ (x :: (right ++ [b])) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc]
  have hleft : ∀ z ∈ left, 0 < z := by
    intro z hz
    apply within_positive hlo hw z
    rw [hm]
    simp [hz]
  have hright : ∀ z ∈ right, 0 < z := by
    intro z hz
    apply within_positive hlo hw z
    rw [hm]
    simp [hz]
  have hpre : DigitsWithin lo hi (a :: left) := by
    intro z hz
    apply hw z
    rw [hesuf]
    exact List.mem_append_left _ hz
  have hsuf : DigitsWithin lo hi (right ++ [b]) := by
    intro z hz
    apply hw z
    rw [hepre]
    exact List.mem_append_right _ hz
  constructor
  · by_contra hax
    have ht := low_weighted_prefix_reverse_lt H hlo left (right ++ [b]) hleft hsuf
      (by simp) (by omega : x < a)
    have hp : ((a :: (left ++ [x])).reverse ++ (right ++ [b])).Perm
        (a :: (mid ++ [b])) := by
      rw [hepre]
      exact (List.reverse_perm _).append_right _
    have hm' := hmin _ hp
    rw [hepre] at hm'
    linarith
  · by_contra hbx
    have ht := low_weighted_suffix_reverse_lt H hlo (a :: left) right hright hpre
      (by simp) (by omega : x < b)
    have hp : ((a :: left) ++ (x :: (right ++ [b])).reverse).Perm
        (a :: (mid ++ [b])) := by
      rw [hesuf]
      exact (List.reverse_perm _).append_left _
    have hm' := hmin _ hp
    rw [hesuf] at hm'
    linarith

/-- Both endpoints of a weighted minimum in a high context are no smaller
than every interior digit. -/
theorem high_weighted_minimum_endpoints {lo hi a b : ℕ} {l r : ℚ} {mid : List ℕ}
    (H : HighBoundaryContext lo hi l r) (hlo : 0 < lo)
    (hw : DigitsWithin lo hi (a :: (mid ++ [b])))
    (hmin : ∀ ds, ds.Perm (a :: (mid ++ [b])) →
      weightedContinuant l r (a :: (mid ++ [b])) ≤ weightedContinuant l r ds) :
    ∀ x ∈ mid, x ≤ a ∧ x ≤ b := by
  intro x hx
  obtain ⟨left, right, hm⟩ := List.mem_iff_append.mp hx
  have hepre : a :: (mid ++ [b]) = (a :: (left ++ [x])) ++ (right ++ [b]) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hesuf : a :: (mid ++ [b]) = (a :: left) ++ (x :: (right ++ [b])) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc]
  have hleft : ∀ z ∈ left, 0 < z := by
    intro z hz
    apply within_positive hlo hw z
    rw [hm]
    simp [hz]
  have hright : ∀ z ∈ right, 0 < z := by
    intro z hz
    apply within_positive hlo hw z
    rw [hm]
    simp [hz]
  have hpre : DigitsWithin lo hi (a :: left) := by
    intro z hz
    apply hw z
    rw [hesuf]
    exact List.mem_append_left _ hz
  have hsuf : DigitsWithin lo hi (right ++ [b]) := by
    intro z hz
    apply hw z
    rw [hepre]
    exact List.mem_append_right _ hz
  constructor
  · by_contra hax
    have ht := high_weighted_prefix_reverse_lt H hlo left (right ++ [b]) hleft hsuf
      (by simp) (by omega : a < x)
    have hp : ((a :: (left ++ [x])).reverse ++ (right ++ [b])).Perm
        (a :: (mid ++ [b])) := by
      rw [hepre]
      exact (List.reverse_perm _).append_right _
    have hm' := hmin _ hp
    rw [hepre] at hm'
    linarith
  · by_contra hbx
    have ht := high_weighted_suffix_reverse_lt H hlo (a :: left) right hright hpre
      (by simp) (by omega : b < x)
    have hp : ((a :: left) ++ (x :: (right ++ [b])).reverse).Perm
        (a :: (mid ++ [b])) := by
      rw [hesuf]
      exact (List.reverse_perm _).append_left _
    have hm' := hmin _ hp
    rw [hesuf] at hm'
    linarith

/-- Uniform endpoint classification for the alternating induction. -/
theorem ramharter_weighted_minimum_endpoints {high : Bool} {lo hi a b : ℕ}
    {l r : ℚ} {mid : List ℕ}
    (H : RamharterContext high lo hi l r) (hlo : 0 < lo)
    (hw : DigitsWithin lo hi (a :: (mid ++ [b])))
    (hmin : ∀ ds, ds.Perm (a :: (mid ++ [b])) →
      weightedContinuant l r (a :: (mid ++ [b])) ≤ weightedContinuant l r ds) :
    ∀ x ∈ mid, ramharterKey high a ≤ ramharterKey high x ∧
      ramharterKey high b ≤ ramharterKey high x := by
  cases high
  · intro x hx
    simpa [ramharterKey] using low_weighted_minimum_endpoints H hlo hw hmin x hx
  · intro x hx
    simpa [ramharterKey] using high_weighted_minimum_endpoints H hlo hw hmin x hx

end Lsbgcd
