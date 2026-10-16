module

public import Lsbgcd.RamharterBoundary

@[expose] public section

/-! # Alternating endpoint choices in the general permutation proof -/
namespace Lsbgcd

/-- Ascending order for low boundaries, descending order for high ones. -/
def ramharterKey (high : Bool) (a : ℕ) : ℤ := if high then -(a : ℤ) else a

def RamharterContext (high : Bool) (lo hi : ℕ) (l r : ℚ) : Prop :=
  if high then HighBoundaryContext lo hi l r else LowBoundaryContext lo hi l r

theorem ramharterKey_injective (high : Bool) : Function.Injective (ramharterKey high) := by
  intro a b h
  cases high <;> simpa [ramharterKey] using h

theorem ramharterKey_flip (high : Bool) (a b : ℕ) :
    ramharterKey (!high) a ≤ ramharterKey (!high) b ↔
      ramharterKey high b ≤ ramharterKey high a := by
  cases high <;> simp [ramharterKey]

theorem RamharterContext.nonneg_left {high : Bool} {lo hi : ℕ} {l r : ℚ}
    (H : RamharterContext high lo hi l r) : 0 ≤ l := by
  cases high
  · exact LowBoundaryContext.nonneg_left H
  · exact HighBoundaryContext.nonneg_left H

theorem RamharterContext.nonneg_right {high : Bool} {lo hi : ℕ} {l r : ℚ}
    (H : RamharterContext high lo hi l r) : 0 ≤ r := by
  cases high
  · exact LowBoundaryContext.nonneg_right H
  · exact HighBoundaryContext.nonneg_right H

/-- Reversing the remaining sorted list flips the next extreme to choose. -/
theorem ramharterKey_reverse_sorted {high : Bool} {as : List ℕ}
    (h : as.Pairwise (fun a b => ramharterKey high a ≤ ramharterKey high b)) :
    as.reverse.Pairwise (fun a b => ramharterKey (!high) a ≤ ramharterKey (!high) b) := by
  rw [List.pairwise_reverse]
  exact h.imp (fun hab => (ramharterKey_flip high _ _).2 hab)

/-- Removing the first two entries in the current order updates both
boundaries and tightens the interval for the remaining reversed list. -/
theorem ramharterContext_step {high : Bool} {lo hi a b : ℕ} {l r : ℚ}
    {rest : List ℕ} (H : RamharterContext high lo hi l r) (hlo : 0 < lo)
    (hwithin : DigitsWithin lo hi (a :: b :: rest))
    (hsorted : (a :: b :: rest).Pairwise
      (fun x y => ramharterKey high x ≤ ramharterKey high y)) :
    RamharterContext (!high) (if high then lo else b) (if high then b else hi)
        (1 / ((a : ℚ) + l)) (1 / ((b : ℚ) + r)) ∧
      DigitsWithin (if high then lo else b) (if high then b else hi) rest.reverse ∧
      rest.reverse.Pairwise
        (fun x y => ramharterKey (!high) x ≤ ramharterKey (!high) y) := by
  have ha := hwithin a (by simp)
  have hb := hwithin b (by simp)
  obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hsorted
  obtain ⟨hsecond, hrest⟩ := List.pairwise_cons.mp htail
  have hab := hfirst b (by simp)
  have hreverse := ramharterKey_reverse_sorted hrest
  refine ⟨?_, ?_, hreverse⟩
  · cases high
    · apply lowBoundaryContext_step H hlo ha hb hb.1 le_rfl
      · simpa [ramharterKey] using hab
      · exact le_rfl
    · apply highBoundaryContext_step H hlo ha hb le_rfl hb.2
      · simpa [ramharterKey] using hab
      · exact le_rfl
  · intro x hx
    have hx' : x ∈ rest := List.mem_reverse.mp hx
    have hxb := hsecond x hx'
    have hxw := hwithin x (by simp [hx'])
    cases high
    · exact ⟨by simpa [ramharterKey] using hxb, hxw.2⟩
    · exact ⟨hxw.1, by simpa [ramharterKey] using hxb⟩

/-- Symmetric new boundaries can occur only when the old boundaries and
the two chosen endpoints were both equal. -/
theorem ramharterContext_update_eq_iff {high : Bool} {lo hi a b : ℕ} {l r : ℚ}
    (H : RamharterContext high lo hi l r)
    (hab : ramharterKey high a ≤ ramharterKey high b) :
    1 / ((a : ℚ) + l) = 1 / ((b : ℚ) + r) ↔ a = b ∧ l = r := by
  cases high
  · apply ordered_boundary_update_eq_iff
    · simpa [ramharterKey] using hab
    · exact LowBoundaryContext.ordered H
  · have hba : b ≤ a := by simpa [ramharterKey] using hab
    have hh := ordered_boundary_update_eq_iff hba (HighBoundaryContext.ordered H)
    constructor
    · intro he
      obtain ⟨heab, helr⟩ := hh.mp he.symm
      exact ⟨heab.symm, helr.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl

end Lsbgcd
