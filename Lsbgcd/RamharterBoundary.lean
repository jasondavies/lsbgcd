module

public import Lsbgcd.ContinuantOrder

@[expose] public section

/-!
# Rational boundary contexts for the Ramharter induction

Once the induction in `RamharterSort.lean` has fixed some outer digits,
their effect on the continuant is summarised by two rational boundary values
`l` and `r` (see `weightedContinuant`). `boundaryCF w r` is the continued
fraction `1/(w₁ + 1/(w₂ + ⋯ + 1/(wₖ + r)))` whose tail is the boundary `r`.

`LowBoundaryContext lo hi l r` records that `l ≤ r` and that both boundaries
are strictly below the continued fraction of every nonempty word with digits
in `[lo, hi]`, closed with the other boundary. `HighBoundaryContext` is the
mirror image. Removing the two least digits turns a low context into a high
one (`lowBoundaryContext_step`), and removing the two greatest turns it back
(`highBoundaryContext_step`), so the contexts alternate as digits are
stripped. `ordered_boundary_update_eq_iff` isolates the only equality case,
which is the source of reversal symmetry.

`RamharterMatrix` evaluates `boundaryCF` through word matrices, and
`RamharterMode` packages the two contexts under one Boolean flag.
-/
namespace Lsbgcd

/-- Every digit belongs to the remaining closed interval. -/
def DigitsWithin (lo hi : ℕ) (as : List ℕ) : Prop :=
  ∀ a ∈ as, lo ≤ a ∧ a ≤ hi

namespace DigitsWithin

variable {lo hi : ℕ} {as bs : List ℕ}

/-- Digits from an interval of positive integers are positive. -/
theorem pos (hlo : 0 < lo) (h : DigitsWithin lo hi as) : ∀ a ∈ as, 0 < a :=
  fun a ha => hlo.trans_le (h a ha).1

theorem subset (h : DigitsWithin lo hi as) (hs : bs ⊆ as) : DigitsWithin lo hi bs :=
  fun b hb => h b (hs hb)

theorem widen {lo' hi' : ℕ} (h : DigitsWithin lo' hi' as) (hlo : lo ≤ lo')
    (hhi : hi' ≤ hi) : DigitsWithin lo hi as :=
  fun a ha => ⟨hlo.trans (h a ha).1, (h a ha).2.trans hhi⟩

theorem tail {a : ℕ} (h : DigitsWithin lo hi (a :: as)) : DigitsWithin lo hi as :=
  h.subset (List.subset_cons_self a as)

theorem append_singleton {b : ℕ} (h : DigitsWithin lo hi as) (hb : lo ≤ b ∧ b ≤ hi) :
    DigitsWithin lo hi (as ++ [b]) := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact h z hz
  · rw [List.mem_singleton.mp hz]
    exact hb

theorem reverse (h : DigitsWithin lo hi as) : DigitsWithin lo hi as.reverse :=
  h.subset fun _ hx => List.mem_reverse.mp hx

end DigitsWithin

/-- Continued fraction with a rational terminal boundary value. -/
def boundaryCF : List ℕ → ℚ → ℚ
  | [], r => r
  | a :: as, r => 1 / ((a : ℚ) + boundaryCF as r)

@[simp] theorem boundaryCF_nil (r : ℚ) : boundaryCF [] r = r := rfl
@[simp] theorem boundaryCF_cons (a : ℕ) (as : List ℕ) (r : ℚ) :
    boundaryCF (a :: as) r = 1 / ((a : ℚ) + boundaryCF as r) := rfl

/-- Appending a word composes its terminal-boundary transformation. -/
theorem boundaryCF_append (as bs : List ℕ) (r : ℚ) :
    boundaryCF (as ++ bs) r = boundaryCF as (boundaryCF bs r) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, boundaryCF_cons, ih]

theorem boundaryCF_nonneg (as : List ℕ) {r : ℚ} (hr : 0 ≤ r) :
    0 ≤ boundaryCF as r := by
  induction as with
  | nil => exact hr
  | cons a as ih =>
    rw [boundaryCF_cons]
    positivity

theorem boundaryCF_pos {as : List ℕ} {r : ℚ} (hr : 0 ≤ r)
    (hpos : ∀ a ∈ as, 0 < a) (hne : as ≠ []) : 0 < boundaryCF as r := by
  cases as with
  | nil => contradiction
  | cons a as =>
    have ha : (0 : ℚ) < a := by exact_mod_cast hpos a (by simp)
    have ht := boundaryCF_nonneg as hr
    rw [boundaryCF_cons]
    positivity

/-- Low exterior boundaries are strictly below every nonempty interior
continued fraction from the remaining alphabet. -/
structure LowBoundaryContext (lo hi : ℕ) (l r : ℚ) : Prop where
  nonneg_left : 0 ≤ l
  nonneg_right : 0 ≤ r
  ordered : l ≤ r
  envelope : ∀ w, DigitsWithin lo hi w → w ≠ [] →
    l < boundaryCF w r ∧ r < boundaryCF w l

/-- High exterior boundaries are strictly above those same interior values. -/
structure HighBoundaryContext (lo hi : ℕ) (l r : ℚ) : Prop where
  nonneg_left : 0 ≤ l
  nonneg_right : 0 ≤ r
  ordered : r ≤ l
  envelope : ∀ w, DigitsWithin lo hi w → w ≠ [] →
    boundaryCF w r < l ∧ boundaryCF w l < r

/-- Ordinary continuants start with two zero boundary values. -/
theorem lowBoundaryContext_zero {lo hi : ℕ} (hlo : 0 < lo) :
    LowBoundaryContext lo hi 0 0 := by
  refine ⟨le_rfl, le_rfl, le_rfl, ?_⟩
  intro w hw hn
  have h := boundaryCF_pos (by norm_num : (0 : ℚ) ≤ 0) (hw.pos hlo) hn
  exact ⟨h, h⟩

/-- Removing the two least digits changes a low context into a high context.
The remaining alphabet may be tightened to any contained interval. -/
theorem lowBoundaryContext_step {lo hi lo' hi' a b : ℕ} {l r : ℚ}
    (H : LowBoundaryContext lo hi l r) (hlo : 0 < lo)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hlo' : lo ≤ lo') (hhi' : hi' ≤ hi) (hab : a ≤ b) (hbnew : b ≤ lo') :
    HighBoundaryContext lo' hi' (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) := by
  have hap : (0 : ℚ) < a := by exact_mod_cast hlo.trans_le ha.1
  have hbp : (0 : ℚ) < b := by exact_mod_cast hlo.trans_le hb.1
  have hal : 0 < (a : ℚ) + l := add_pos_of_pos_of_nonneg hap H.nonneg_left
  have hbr : 0 < (b : ℚ) + r := add_pos_of_pos_of_nonneg hbp H.nonneg_right
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hal (add_le_add hab' H.ordered)
  · intro w hw hn
    cases w with
    | nil => contradiction
    | cons x xs =>
      have hxs := hw.tail.widen hlo' hhi'
      have hleft := (H.envelope (xs ++ [b]) (hxs.append_singleton hb) (by simp)).1
      have hright := (H.envelope (xs ++ [a]) (hxs.append_singleton ha) (by simp)).2
      simp only [boundaryCF_append, boundaryCF_cons, boundaryCF_nil] at hleft hright
      have hbx' : (b : ℚ) ≤ x := by exact_mod_cast hbnew.trans (hw x (by simp)).1
      simp only [boundaryCF_cons]
      constructor
      · apply one_div_lt_one_div_of_lt hal
        linarith
      · apply one_div_lt_one_div_of_lt hbr
        linarith

/-- Removing the two greatest digits changes a high context into a low
context. Strictness survives even when the selected digit values coincide. -/
theorem highBoundaryContext_step {lo hi lo' hi' a b : ℕ} {l r : ℚ}
    (H : HighBoundaryContext lo hi l r) (hlo : 0 < lo)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hlo' : lo ≤ lo') (hhi' : hi' ≤ hi) (hba : b ≤ a) (hbnew : hi' ≤ b) :
    LowBoundaryContext lo' hi' (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) := by
  have hap : (0 : ℚ) < a := by exact_mod_cast hlo.trans_le ha.1
  have hbp : (0 : ℚ) < b := by exact_mod_cast hlo.trans_le hb.1
  have hal : 0 < (a : ℚ) + l := add_pos_of_pos_of_nonneg hap H.nonneg_left
  have hbr : 0 < (b : ℚ) + r := add_pos_of_pos_of_nonneg hbp H.nonneg_right
  have hba' : (b : ℚ) ≤ a := by exact_mod_cast hba
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hbr (add_le_add hba' H.ordered)
  · intro w hw hn
    cases w with
    | nil => contradiction
    | cons x xs =>
      have hxp : (0 : ℚ) < x := by exact_mod_cast hw.pos (hlo.trans_le hlo') x (by simp)
      have hxs := hw.tail.widen hlo' hhi'
      have hleft := (H.envelope (xs ++ [b]) (hxs.append_singleton hb) (by simp)).1
      have hright := (H.envelope (xs ++ [a]) (hxs.append_singleton ha) (by simp)).2
      simp only [boundaryCF_append, boundaryCF_cons, boundaryCF_nil] at hleft hright
      have hxb' : (x : ℚ) ≤ b := by exact_mod_cast (hw x (by simp)).2.trans hbnew
      have htl := boundaryCF_nonneg xs (le_of_lt (one_div_pos.mpr hal))
      have htr := boundaryCF_nonneg xs (le_of_lt (one_div_pos.mpr hbr))
      simp only [boundaryCF_cons]
      constructor
      · apply one_div_lt_one_div_of_lt (add_pos_of_pos_of_nonneg hxp htr)
        linarith
      · apply one_div_lt_one_div_of_lt (add_pos_of_pos_of_nonneg hxp htl)
        linarith

/-- Equality of updated boundaries forces equality of both selected digits
and of the old boundaries; this is the only source of reversal symmetry. -/
theorem ordered_boundary_update_eq_iff {a b : ℕ} {l r : ℚ}
    (hab : a ≤ b) (hlr : l ≤ r) :
    1 / ((a : ℚ) + l) = 1 / ((b : ℚ) + r) ↔ a = b ∧ l = r := by
  constructor
  · intro he
    have hs : (a : ℚ) + l = b + r := by
      have hh := congrArg (fun x : ℚ => x⁻¹) he
      simpa only [one_div, inv_inv] using hh
    have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
    have heab : (a : ℚ) = b := by linarith
    exact ⟨by exact_mod_cast heab, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Lsbgcd
