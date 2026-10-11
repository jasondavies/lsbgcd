import Lsbgcd.ContinuantOrder

/-!
# Alternating boundary inequalities for continuant minimisation

The two boundary words in Kan's Lemma 4.6 can be compared uniformly over
all intervening words whose digits stay inside the remaining rank interval.
The invariant alternates as a largest and a smallest digit are stripped.
Equality is retained as a word identity, rather than relying on injectivity
of finite continued fractions (which fails without endpoint conventions).
-/
namespace Lsbgcd

/-- The rational continued fraction `[0; as]`. -/
def reciprocalConvergent (as : List ℕ) : ℚ :=
  (convergent as).2 / (convergent as).1

@[simp] theorem reciprocalConvergent_nil : reciprocalConvergent [] = 0 := by
  norm_num [reciprocalConvergent, convergent]

theorem reciprocalConvergent_nonneg (as : List ℕ) : 0 ≤ reciprocalConvergent as := by
  unfold reciprocalConvergent
  positivity

theorem reciprocalConvergent_pos {as : List ℕ} (hpos : ∀ a ∈ as, 0 < a)
    (hne : as ≠ []) : 0 < reciprocalConvergent as := by
  have hp := positive_convergent hpos
  have hq := positive_convergent_denominator hpos hne
  unfold reciprocalConvergent
  exact div_pos (by exact_mod_cast hq) (by exact_mod_cast hp.1)

theorem reciprocalConvergent_eq_zero_iff {as : List ℕ} (hpos : ∀ a ∈ as, 0 < a) :
    reciprocalConvergent as = 0 ↔ as = [] := by
  constructor
  · intro h
    by_contra hn
    have := reciprocalConvergent_pos hpos hn
    linarith
  · rintro rfl
    exact reciprocalConvergent_nil

theorem reciprocalConvergent_cons {as : List ℕ} {a : ℕ}
    (ha : 0 < a) (hpos : ∀ b ∈ as, 0 < b) :
    reciprocalConvergent (a :: as) = 1 / ((a : ℚ) + reciprocalConvergent as) := by
  have hp := (positive_convergent hpos).1
  have hpr : (0 : ℚ) < (convergent as).1 := by exact_mod_cast hp
  have har : (0 : ℚ) < a := by exact_mod_cast ha
  unfold reciprocalConvergent
  simp only [convergent, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- Increasing both the leading digit and the tail fraction decreases the
reciprocal fraction. Equality forces equality in both comparisons. -/
theorem reciprocalConvergent_cons_compare {as bs : List ℕ} {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hapos : ∀ x ∈ as, 0 < x) (hbpos : ∀ x ∈ bs, 0 < x)
    (hab : a ≤ b) (ht : reciprocalConvergent as ≤ reciprocalConvergent bs) :
    reciprocalConvergent (b :: bs) ≤ reciprocalConvergent (a :: as) ∧
      (reciprocalConvergent (b :: bs) = reciprocalConvergent (a :: as) →
        a = b ∧ reciprocalConvergent bs = reciprocalConvergent as) := by
  rw [reciprocalConvergent_cons hb hbpos, reciprocalConvergent_cons ha hapos]
  have hapos' : 0 < (a : ℚ) + reciprocalConvergent as :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast ha) (reciprocalConvergent_nonneg _)
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hs : (a : ℚ) + reciprocalConvergent as ≤ b + reciprocalConvergent bs := by
    linarith
  constructor
  · exact one_div_le_one_div_of_le hapos' hs
  · intro he
    have hsum : (b : ℚ) + reciprocalConvergent bs = a + reciprocalConvergent as := by
      have hh := congrArg (fun x : ℚ => x⁻¹) he
      simpa only [one_div, inv_inv] using hh
    have heab : (a : ℚ) = b := by linarith
    exact ⟨by exact_mod_cast heab, by linarith⟩

/-- Every digit belongs to the remaining closed interval. -/
def DigitsWithin (lo hi : ℕ) (as : List ℕ) : Prop :=
  ∀ a ∈ as, lo ≤ a ∧ a ≤ hi

/-- Upper boundary inequality, with its sharp equality condition. -/
def UpperBoundary (left right : List ℕ) (lo hi : ℕ) : Prop :=
  ∀ mid, DigitsWithin lo hi mid →
    reciprocalConvergent (mid ++ right) ≤ reciprocalConvergent left ∧
      (reciprocalConvergent (mid ++ right) = reciprocalConvergent left →
        mid ++ right = left)

/-- Lower boundary inequality, with the same equality condition. -/
def LowerBoundary (left right : List ℕ) (lo hi : ℕ) : Prop :=
  ∀ mid, DigitsWithin lo hi mid →
    reciprocalConvergent left ≤ reciprocalConvergent (mid ++ right) ∧
      (reciprocalConvergent (mid ++ right) = reciprocalConvergent left →
        mid ++ right = left)

/-- The least first digit starts the alternating boundary invariant. -/
theorem upperBoundary_singleton {a lo hi : ℕ} (ha : 0 < a) (halo : a ≤ lo) :
    UpperBoundary [a] [] lo hi := by
  intro mid hm
  simp only [List.append_nil]
  cases mid with
  | nil =>
    have hp := reciprocalConvergent_pos (as := [a]) (by simpa using ha) (by simp)
    constructor
    · simpa using le_of_lt hp
    · intro he
      simp only [reciprocalConvergent_nil] at he
      linarith
  | cons b bs =>
    have hab : a ≤ b := halo.trans (hm b (by simp)).1
    have hpos : ∀ x ∈ bs, 0 < x := by
      intro x hx
      have := (hm x (by simp [hx])).1
      omega
    have hbp : 0 < b := by omega
    obtain ⟨hle, he⟩ := reciprocalConvergent_cons_compare ha hbp
      (by simp : ∀ x ∈ ([] : List ℕ), 0 < x) hpos hab
      (by simpa using reciprocalConvergent_nonneg bs)
    refine ⟨hle, ?_⟩
    intro hh
    obtain ⟨hab', ht⟩ := he hh
    have hnil : bs = [] := (reciprocalConvergent_eq_zero_iff hpos).1 (by simpa using ht)
    simp [hnil, hab']

/-- Adding the next greatest digit on the left and next least digit on the
right turns an upper boundary into a lower boundary. Only interval containment
and the indicated endpoint orders are needed. -/
theorem upperBoundary_step {left right : List ℕ} {lo hi lo' hi' d b : ℕ}
    (hl : ∀ x ∈ left, 0 < x) (hr : ∀ x ∈ right, 0 < x)
    (hlo : 0 < lo) (hlo' : lo ≤ lo') (hhi' : hi' ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) (hd : 0 < d) (hbd : b ≤ d) (hmax : hi' ≤ d)
    (H : UpperBoundary left right lo hi) :
    LowerBoundary (d :: left) (b :: right) lo' hi' := by
  intro mid hm
  have hbp : 0 < b := by omega
  have hmpos : ∀ x ∈ mid, 0 < x := by
    intro x hx
    have := (hm x hx).1
    omega
  cases mid with
  | nil =>
    obtain ⟨hle, he⟩ := H [] (by simp [DigitsWithin])
    simp only [List.nil_append] at hle he ⊢
    obtain ⟨hout, houtEq⟩ := reciprocalConvergent_cons_compare hbp hd hr hl hbd hle
    refine ⟨hout, ?_⟩
    intro hh
    obtain ⟨hbd', ht⟩ := houtEq hh.symm
    have hw := he ht.symm
    simp only [hbd', hw]
  | cons x xs =>
    have hwithin : DigitsWithin lo hi (xs ++ [b]) := by
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · have hz' := hm z (by simp [hz])
        constructor <;> omega
      · exact hb
    obtain ⟨hle, he⟩ := H (xs ++ [b]) hwithin
    have happ : (xs ++ [b]) ++ right = xs ++ b :: right := by simp
    rw [happ] at hle he
    have htail : ∀ z ∈ xs ++ b :: right, 0 < z := by
      intro z hz
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | rfl | hz
      · exact hmpos z (by simp [hz])
      · exact hbp
      · exact hr z hz
    have hx : 0 < x := hmpos x (by simp)
    have hxd : x ≤ d := (hm x (by simp)).2.trans hmax
    obtain ⟨hout, houtEq⟩ := reciprocalConvergent_cons_compare hx hd htail hl hxd hle
    change reciprocalConvergent (d :: left) ≤ reciprocalConvergent (x :: (xs ++ b :: right)) ∧ _
    refine ⟨hout, ?_⟩
    intro hh
    obtain ⟨hxd', ht⟩ := houtEq hh.symm
    have hw := he ht.symm
    simp only [List.cons_append, hxd', hw]

/-- The next least left digit and greatest right digit turn a lower boundary
back into an upper boundary. -/
theorem lowerBoundary_step {left right : List ℕ} {lo hi lo' hi' a c : ℕ}
    (hl : ∀ x ∈ left, 0 < x) (hr : ∀ x ∈ right, 0 < x)
    (_hlo : 0 < lo) (hlo' : lo ≤ lo') (hhi' : hi' ≤ hi)
    (hc : lo ≤ c ∧ c ≤ hi) (ha : 0 < a) (hac : a ≤ c) (hmin : a ≤ lo')
    (H : LowerBoundary left right lo hi) :
    UpperBoundary (a :: left) (c :: right) lo' hi' := by
  intro mid hm
  have hcp : 0 < c := by omega
  have hmpos : ∀ x ∈ mid, 0 < x := by
    intro x hx
    have := (hm x hx).1
    omega
  cases mid with
  | nil =>
    obtain ⟨hle, he⟩ := H [] (by simp [DigitsWithin])
    simp only [List.nil_append] at hle he ⊢
    obtain ⟨hout, houtEq⟩ := reciprocalConvergent_cons_compare ha hcp hl hr hac hle
    refine ⟨hout, ?_⟩
    intro hh
    obtain ⟨hac', ht⟩ := houtEq hh
    have hw := he ht
    simp only [hac', hw]
  | cons x xs =>
    have hwithin : DigitsWithin lo hi (xs ++ [c]) := by
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · have hz' := hm z (by simp [hz])
        constructor <;> omega
      · exact hc
    obtain ⟨hle, he⟩ := H (xs ++ [c]) hwithin
    have happ : (xs ++ [c]) ++ right = xs ++ c :: right := by simp
    rw [happ] at hle he
    have htail : ∀ z ∈ xs ++ c :: right, 0 < z := by
      intro z hz
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | rfl | hz
      · exact hmpos z (by simp [hz])
      · exact hcp
      · exact hr z hz
    have hx : 0 < x := hmpos x (by simp)
    have hax : a ≤ x := hmin.trans (hm x (by simp)).1
    obtain ⟨hout, houtEq⟩ := reciprocalConvergent_cons_compare ha hx hl htail hax hle
    change reciprocalConvergent (x :: (xs ++ c :: right)) ≤ reciprocalConvergent (a :: left) ∧ _
    refine ⟨hout, ?_⟩
    intro hh
    obtain ⟨hax', ht⟩ := houtEq hh
    have hw := he ht
    simp only [List.cons_append, ← hax', hw]


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
  have hp : ∀ a ∈ w, 0 < a := by
    intro a ha
    exact hlo.trans_le (hw a ha).1
  have h := boundaryCF_pos (by norm_num : (0 : ℚ) ≤ 0) hp hn
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
      have hxs : DigitsWithin lo hi xs := by
        intro z hz
        have hh := hw z (by simp [hz])
        constructor <;> omega
      have hwb : DigitsWithin lo hi (xs ++ [b]) := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hxs z hz
        · exact hb
      have hwa : DigitsWithin lo hi (xs ++ [a]) := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hxs z hz
        · exact ha
      have hleft := (H.envelope (xs ++ [b]) hwb (by simp)).1
      have hright := (H.envelope (xs ++ [a]) hwa (by simp)).2
      simp only [boundaryCF_append, boundaryCF_cons, boundaryCF_nil] at hleft hright
      have hbx : b ≤ x := hbnew.trans (hw x (by simp)).1
      have hbx' : (b : ℚ) ≤ x := by exact_mod_cast hbx
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
      have hxp : (0 : ℚ) < x := by
        have hh := (hw x (by simp)).1
        exact_mod_cast (show 0 < x by omega)
      have hxs : DigitsWithin lo hi xs := by
        intro z hz
        have hh := hw z (by simp [hz])
        constructor <;> omega
      have hwb : DigitsWithin lo hi (xs ++ [b]) := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hxs z hz
        · exact hb
      have hwa : DigitsWithin lo hi (xs ++ [a]) := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hxs z hz
        · exact ha
      have hleft := (H.envelope (xs ++ [b]) hwb (by simp)).1
      have hright := (H.envelope (xs ++ [a]) hwa (by simp)).2
      simp only [boundaryCF_append, boundaryCF_cons, boundaryCF_nil] at hleft hright
      have hxb : x ≤ b := (hw x (by simp)).2.trans hbnew
      have hxb' : (x : ℚ) ≤ b := by exact_mod_cast hxb
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
