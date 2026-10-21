module

public import Lsbgcd.RamharterWeighted
public import Lsbgcd.RamharterMatrix
public import Lsbgcd.RamharterMode

@[expose] public section

/-!
# Extremal endpoints of weighted permutation minima

In a boundary context, reversing a prefix or suffix whose endpoints are out
of order strictly decreases the weighted continuant. Hence both endpoints of
a weighted minimum are the two least digits in a low context and the two
greatest in a high context (`ramharter_weighted_minimum_endpoints`), and the
endpoints are oriented by the context unless the boundaries are equal
(`ramharter_weighted_endpoint_order`). `RamharterSort.lean` uses both
results in each step of its induction.
-/
namespace Lsbgcd

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
  have hh := (boundary_matrix_compare_rev hpos hr).1 h
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
  have hf := boundary_factor_positive (hsuffix.pos hlo) H.nonneg_right
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
  have hf := boundary_factor_negative (hsuffix.pos hlo) H.nonneg_right
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
  have hf := boundary_factor_positive (hpre.reverse.pos hlo) H.nonneg_left
    (H.envelope pre.reverse hpre.reverse (by simpa using hne)).2
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
  have hf := boundary_factor_negative (hpre.reverse.pos hlo) H.nonneg_left
    (H.envelope pre.reverse hpre.reverse (by simpa using hne)).2
  rw [wordMatrix_reverse] at hf
  simp only [Matrix.transpose_apply] at hf
  have hpos : 0 < r * ((wordMatrix pre 0 0 : ℚ) + l * (wordMatrix pre 1 0 : ℚ)) -
      ((wordMatrix pre 0 1 : ℚ) + l * (wordMatrix pre 1 1 : ℚ)) := by linarith
  have hs := endpoint_skew_pos hmid hyx
  have hd := weightedContinuant_reverse_suffix_difference l r pre (x :: (mid ++ [y]))
  have hp := mul_pos hs hpos
  linarith

/-- Split a minimum `a :: (mid ++ [b])` at an interior digit `x`, and record
that neither the prefix through `x` nor the suffix from `x` can be reversed
to a smaller value. Both endpoint theorems below start from this. -/
private theorem weighted_minimum_split {lo hi a b x : ℕ} {l r : ℚ} {mid : List ℕ}
    (hlo : 0 < lo) (hw : DigitsWithin lo hi (a :: (mid ++ [b])))
    (hmin : ∀ ds, ds.Perm (a :: (mid ++ [b])) →
      weightedContinuant l r (a :: (mid ++ [b])) ≤ weightedContinuant l r ds)
    (hx : x ∈ mid) :
    ∃ left right, (∀ z ∈ left, 0 < z) ∧ (∀ z ∈ right, 0 < z) ∧
      DigitsWithin lo hi (a :: left) ∧ DigitsWithin lo hi (right ++ [b]) ∧
      weightedContinuant l r ((a :: (left ++ [x])) ++ (right ++ [b])) ≤
        weightedContinuant l r ((a :: (left ++ [x])).reverse ++ (right ++ [b])) ∧
      weightedContinuant l r ((a :: left) ++ (x :: (right ++ [b]))) ≤
        weightedContinuant l r ((a :: left) ++ (x :: (right ++ [b])).reverse) := by
  obtain ⟨left, right, hm⟩ := List.mem_iff_append.mp hx
  have hepre : a :: (mid ++ [b]) = (a :: (left ++ [x])) ++ (right ++ [b]) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hesuf : a :: (mid ++ [b]) = (a :: left) ++ (x :: (right ++ [b])) := by
    rw [hm]
    simp only [List.cons_append, List.append_assoc]
  have hpos := hw.pos hlo
  refine ⟨left, right, fun z hz => hpos z (by rw [hm]; simp [hz]),
    fun z hz => hpos z (by rw [hm]; simp [hz]),
    hw.subset (by rw [hesuf]; exact List.subset_append_left _ _),
    hw.subset (by rw [hepre]; exact List.subset_append_right _ _), ?_, ?_⟩
  · have h := hmin ((a :: (left ++ [x])).reverse ++ (right ++ [b]))
      (by rw [hepre]; exact (List.reverse_perm _).append_right _)
    rwa [hepre] at h
  · have h := hmin ((a :: left) ++ (x :: (right ++ [b])).reverse)
      (by rw [hesuf]; exact (List.reverse_perm _).append_left _)
    rwa [hesuf] at h

/-- Both endpoints of a weighted minimum in a low context are no greater
than every interior digit. -/
theorem low_weighted_minimum_endpoints {lo hi a b : ℕ} {l r : ℚ} {mid : List ℕ}
    (H : LowBoundaryContext lo hi l r) (hlo : 0 < lo)
    (hw : DigitsWithin lo hi (a :: (mid ++ [b])))
    (hmin : ∀ ds, ds.Perm (a :: (mid ++ [b])) →
      weightedContinuant l r (a :: (mid ++ [b])) ≤ weightedContinuant l r ds) :
    ∀ x ∈ mid, a ≤ x ∧ b ≤ x := by
  intro x hx
  obtain ⟨left, right, hleft, hright, hpre, hsuf, hp, hs⟩ :=
    weighted_minimum_split hlo hw hmin hx
  constructor
  · by_contra hax
    have ht := low_weighted_prefix_reverse_lt H hlo left (right ++ [b]) hleft hsuf
      (by simp) (by omega : x < a)
    linarith
  · by_contra hbx
    have ht := low_weighted_suffix_reverse_lt H hlo (a :: left) right hright hpre
      (by simp) (by omega : x < b)
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
  obtain ⟨left, right, hleft, hright, hpre, hsuf, hp, hs⟩ :=
    weighted_minimum_split hlo hw hmin hx
  constructor
  · by_contra hax
    have ht := high_weighted_prefix_reverse_lt H hlo left (right ++ [b]) hleft hsuf
      (by simp) (by omega : a < x)
    linarith
  · by_contra hbx
    have ht := high_weighted_suffix_reverse_lt H hlo (a :: left) right hright hpre
      (by simp) (by omega : b < x)
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

/-- A weighted minimum has its endpoints in the current rank order, except
when the two equal boundaries permit reversal without changing the value. -/
theorem ramharter_weighted_endpoint_order {high : Bool} {lo hi a b : ℕ} {l r : ℚ}
    {mid : List ℕ} (H : RamharterContext high lo hi l r)
    (hmid : ∀ x ∈ mid, 0 < x)
    (hmin : weightedContinuant l r (a :: (mid ++ [b])) ≤
      weightedContinuant l r (a :: (mid ++ [b])).reverse) :
    ramharterKey high a ≤ ramharterKey high b ∨ l = r := by
  cases high
  · have h := weightedContinuant_low_endpoint_order mid hmid
      (LowBoundaryContext.ordered H) hmin
    simpa [ramharterKey] using h
  · have h := weightedContinuant_high_endpoint_order mid hmid
      (HighBoundaryContext.ordered H) hmin
    simpa [ramharterKey] using h

end Lsbgcd
