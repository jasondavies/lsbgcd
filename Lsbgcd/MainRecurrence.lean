import Lsbgcd.Specification

/-! # The order-16 recurrence for the candidate sequences -/
namespace Lsbgcd

theorem order16_of_subsequences (f : ℕ → ℤ)
    (ho : ∀ k, f (2 * (k + 2) + 1) + f (2 * k + 1) = 4 * f (2 * (k + 1) + 1))
    (he : ∀ k, f (4 * (k + 3)) + 15 * f (4 * (k + 1)) =
      15 * f (4 * (k + 2)) + f (4 * k))
    (ht : ∀ k, f (4 * (k + 3) + 2) + 15 * f (4 * (k + 1) + 2) =
      15 * f (4 * (k + 2) + 2) + f (4 * k + 2)) : Order16 f := by
  have oddRec (n : ℕ) (hn : n % 2 = 1) : f (n + 4) + f n = 4 * f (n + 2) := by
    have h : n = 2 * (n / 2) + 1 := by omega
    rw [h]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho (n / 2)
  have evenRec (n : ℕ) (hn : n % 2 = 0) :
      f (n + 12) + 15 * f (n + 4) = 15 * f (n + 8) + f n := by
    have cases : n % 4 = 0 ∨ n % 4 = 2 := by omega
    rcases cases with h | h
    · have hn' : n = 4 * (n / 4) := by omega
      rw [hn']
      simpa [Nat.mul_add] using he (n / 4)
    · have hn' : n = 4 * (n / 4) + 2 := by omega
      rw [hn']
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht (n / 4)
  intro n
  by_cases hn : n % 2 = 0
  · have h0 := evenRec n hn
    have h2 := evenRec (n + 2) (by omega)
    have h4 := evenRec (n + 4) (by omega)
    norm_num only [Nat.add_assoc] at h2 h4
    linear_combination h4 - 4 * h2 + h0
  · have h0 := oddRec n (by omega)
    have h4 := oddRec (n + 4) (by omega)
    have h8 := oddRec (n + 8) (by omega)
    have h12 := oddRec (n + 12) (by omega)
    norm_num only [Nat.add_assoc] at h4 h8 h12
    linear_combination h12 - 15 * h8 + 15 * h4 - h0

theorem candidate_x_order16 : Order16 (fun n => (candidate n).1) := by
  apply order16_of_subsequences
  · intro k; exact_mod_cast (candidate_odd_recurrence k).1
  · intro k; exact_mod_cast (candidate_even_recurrence k).1
  · intro k; exact_mod_cast (candidate_offset_recurrence k).1

theorem candidate_y_order16 : Order16 (fun n => (candidate n).2) := by
  apply order16_of_subsequences
  · intro k; exact_mod_cast (candidate_odd_recurrence k).2
  · intro k; exact_mod_cast (candidate_even_recurrence k).2
  · intro k; exact_mod_cast (candidate_offset_recurrence k).2

end Lsbgcd
