module

public import Lsbgcd.Steps
public import Lsbgcd.ContinuantOrder

@[expose] public section

/-! # Valid continued-fraction words and exact iteration counts (§§3,5) -/
namespace Lsbgcd

theorem inverseA_ordered (e x y : ℕ) : x ≤ 2 ^ e * x + y := by
  have : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by decide)
  nlinarith

theorem step_inverseA {e x y : ℕ} (hx : 0 < x) (hxy : y ≤ x)
    (h : 2 * y ≤ 2 ^ e * x) : step (2 ^ e * x + y) x = (x, y) := by
  have hc := (lemma3_1 hx).2 h
  have hs := choosesA_step hc
  simpa [inverseA, max_eq_left hxy, min_eq_right hxy] using hs

theorem iterations_inverseA {e x y : ℕ} (hx : 0 < x) (hxy : y ≤ x)
    (h : 2 * y ≤ 2 ^ e * x) :
    iterations (2 ^ e * x + y) x = iterations x y + 1 := by
  rw [iterations_of_ordered (inverseA_ordered e x y), run]
  simp only [dite_eq_right (Nat.ne_of_gt hx)]
  simp only [step_inverseA hx hxy h]
  rw [iterations_of_ordered hxy]

theorem admissible_head {a : ℕ} {as : List ℕ} (h : Admissible (a :: as)) :
    a = 1 ∨ a = 2 := by
  cases as with
  | nil => exact h
  | cons b bs => exact h.1

theorem admissible_tail {a : ℕ} {as : List ℕ} (h : Admissible (a :: as)) :
    Admissible as := by
  cases as with
  | nil => trivial
  | cons b bs => exact h.2.2

theorem admissible_digits {as : List ℕ} (h : Admissible as) :
    ∀ a ∈ as, a = 1 ∨ a = 2 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact admissible_head h
    · exact ih (admissible_tail h) b hb

theorem admissible_convergent {as : List ℕ} (h : Admissible as) :
    0 < (convergent as).1 ∧ (convergent as).2 ≤ (convergent as).1 :=
  positive_convergent fun a ha => by rcases admissible_digits h a ha with rfl | rfl <;> decide

theorem admissible_one_bound {as : List ℕ} (h : Admissible (1 :: as)) :
    2 * (convergent as).2 ≤ (convergent as).1 := by
  cases as with
  | nil => norm_num [convergent]
  | cons b bs =>
    have hb := admissible_head (admissible_tail h)
    have hn : ¬(1 = 1 ∧ b = 1) := h.2.1
    have : b = 2 := by omega
    subst b
    simp only [convergent]
    omega

/-- Every admissible word gives an actual computation of exactly its length.
This supplies the continued-fraction-to-algorithm direction used in §5. -/
theorem admissible_iterations {as : List ℕ} (h : Admissible as) :
    iterations (convergent as).1 (convergent as).2 = as.length := by
  induction as with
  | nil => norm_num [convergent, iterations, run]
  | cons a as ih =>
    have ht := admissible_tail h
    obtain ⟨hx, hxy⟩ := admissible_convergent ht
    have hi := ih ht
    obtain ha | ha := admissible_head h
    · subst a
      have hs := iterations_inverseA (e := 0) hx hxy (by
        simpa using admissible_one_bound h)
      simpa [convergent, hi] using hs
    · subst a
      have hs := iterations_inverseA (e := 1) hx hxy (by simpa using Nat.mul_le_mul_left 2 hxy)
      simpa [convergent, hi] using hs

end Lsbgcd
