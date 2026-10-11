import Lsbgcd.RamharterWeighted
import Lsbgcd.RamharterMode

/-! # Endpoint orientation for the alternating weighted minimum -/
namespace Lsbgcd

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

/-- Reversing endpoints that are out of the current rank order never
increases the weighted continuant in either boundary mode. -/
theorem ramharter_weighted_reverse_le {high : Bool} {lo hi a b : ℕ} {l r : ℚ}
    {mid : List ℕ} (H : RamharterContext high lo hi l r)
    (hmid : ∀ x ∈ mid, 0 < x)
    (horder : ramharterKey high b < ramharterKey high a) :
    weightedContinuant l r (a :: (mid ++ [b])).reverse ≤
      weightedContinuant l r (a :: (mid ++ [b])) := by
  cases high
  · exact weightedContinuant_low_reverse_le mid hmid (LowBoundaryContext.ordered H)
      (by simpa [ramharterKey] using horder)
  · exact weightedContinuant_high_reverse_le mid hmid (HighBoundaryContext.ordered H)
      (by simpa [ramharterKey] using horder)

end Lsbgcd
