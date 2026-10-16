module

public import Lsbgcd.Validity

@[expose] public section

/-!
# Reduction of arbitrary partial computations (Theorem 4.3)

The output pair is retained exactly. Replace zero-exponent unswapped steps
by A₀ and all other steps by A₁. Corollary 3.4 rules out adjacent A₀ steps,
so Lemma 3.5 proves that the resulting partial computation is valid.
-/
namespace Lsbgcd

def inverseComputation : List Transformation → ℕ × ℕ → ℕ × ℕ
  | [], p => p
  | s :: ss, p => inverseComputation ss (s.inverse p)

namespace Transformation

def reducedExponent : Transformation → ℕ
  | .A e | .B e => if e = 0 then 0 else 1
  | .IA _ | .IB _ => 1

theorem reducedExponent_mem (s : Transformation) :
    reducedExponent s = 0 ∨ reducedExponent s = 1 := by
  cases s with
  | A e => simp only [reducedExponent]; split_ifs <;> simp
  | B e => simp only [reducedExponent]; split_ifs <;> simp
  | IA e => exact Or.inr rfl
  | IB e => exact Or.inr rfl

theorem reducedExponent_zero_iff (s : Transformation) :
    reducedExponent s = 0 ↔ s = .A 0 ∨ s = .B 0 := by
  cases s with
  | A e => simp [reducedExponent]
  | B e => simp [reducedExponent]
  | IA e => simp [reducedExponent]
  | IB e => simp [reducedExponent]

/-- Each reduced step is valid on the same output pair. -/
theorem reduced_valid {s : Transformation} {p : ℕ × ℕ} (h : s.ValidOn p) :
    ValidOn (.A (reducedExponent s)) p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hxy⟩ := valid_positive_ordered h
  rw [validA_iff]
  refine ⟨hx, hxy, ?_⟩
  cases s with
  | A e =>
    by_cases he : e = 0
    · simpa [reducedExponent, he] using ((validA_iff e x y).1 h).2.2
    · simpa [reducedExponent, he] using Nat.mul_le_mul_left 2 hxy
  | B e =>
    by_cases he : e = 0
    · have hb := ((validB_iff e x y).1 h).2.2.2
      simpa [reducedExponent, he] using le_of_lt hb
    · simpa [reducedExponent, he] using Nat.mul_le_mul_left 2 hxy
  | IA e => simpa [reducedExponent] using Nat.mul_le_mul_left 2 hxy
  | IB e => simpa [reducedExponent] using Nat.mul_le_mul_left 2 hxy

/-- The comparison in Lemma 4.1 covers all four kinds of steps. -/
theorem reduced_smaller {s : Transformation} {p : ℕ × ℕ} (h : s.ValidOn p) :
    Smaller (inverseA (reducedExponent s) p) (s.inverse p) := by
  obtain ⟨x, y⟩ := p
  have hre : ∀ e : ℕ, (if e = 0 then 0 else 1) ≤ e := by
    intro e
    split_ifs <;> omega
  cases s with
  | A e => exact inverseA_mono_exponent (hre e)
  | B e =>
    have h1 := inverseA_mono_exponent (x := x) (y := y) (hre e)
    have h2 := inverseA_smaller_inverseB (le_of_lt ((validB_iff e x y).1 h).2.2.2)
    exact smaller_trans h1 h2
  | IA e =>
    obtain ⟨hxy, hb, _⟩ := (validIA_iff e x y).1 h
    exact inverseA_one_smaller_interchanged (le_of_lt hxy) hb
  | IB e =>
    obtain ⟨hxy, hb, _⟩ := (validIB_iff e x y).1 h
    have h1 := inverseA_one_smaller_interchanged (le_of_lt hxy) (le_of_lt hb)
    have h2 := inverseA_smaller_inverseB (le_of_lt hb)
    exact smaller_trans h1 h2

end Transformation

/-- Corollary 3.4 applies at every position of a valid computation. -/
theorem reduced_noConsecutiveZeros {ss : List Transformation} {p : ℕ × ℕ}
    (h : ValidComputation ss p) :
    NoConsecutiveZeros (ss.map Transformation.reducedExponent) := by
  induction ss generalizing p with
  | nil => trivial
  | cons s ss ih =>
    cases ss with
    | nil => trivial
    | cons t ts =>
      refine ⟨?_, ih h.2⟩
      by_contra hz
      have hs : s = .A 0 ∨ s = .B 0 :=
        (Transformation.reducedExponent_zero_iff s).1 (by omega)
      have ht : t = .A 0 ∨ t = .B 0 :=
        (Transformation.reducedExponent_zero_iff t).1 (by omega)
      have hpair : ValidComputation [s, t] p := ⟨h.1, h.2.1, trivial⟩
      obtain ⟨haa, hab, hba, hbb⟩ := corollary3_4 p
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · exact haa hpair
      · exact hab hpair
      · exact hba hpair
      · exact hbb hpair

theorem reduced_computation_valid {ss : List Transformation} {p : ℕ × ℕ}
    (h : ValidComputation ss p) :
    ValidComputation ((ss.map Transformation.reducedExponent).map Transformation.A) p := by
  cases ss with
  | nil => trivial
  | cons s ss => exact lemma3_5 (reduced_noConsecutiveZeros h) (Transformation.reduced_valid h.1)

theorem reduced_computation_smaller {ss : List Transformation} {p : ℕ × ℕ}
    (h : ValidComputation ss p) :
    Smaller (inverseAs (ss.map Transformation.reducedExponent) p)
      (inverseComputation ss p) := by
  induction ss generalizing p with
  | nil => exact ⟨le_refl _, le_refl _⟩
  | cons s ss ih =>
    simp only [List.map_cons, inverseAs, inverseComputation]
    exact smaller_trans
      (lemma4_2 (ss.map Transformation.reducedExponent)
        (Transformation.reduced_smaller h.1)) (ih h.2)

/-- Theorem 4.3 in full: at any output pair, every valid partial computation
has a valid A₀/A₁ replacement of the same length and no larger input pair. -/
theorem theorem4_3 {ss : List Transformation} {p : ℕ × ℕ}
    (h : ValidComputation ss p) :
    ∃ es : List ℕ, es.length = ss.length ∧
      (∀ e ∈ es, e = 0 ∨ e = 1) ∧
      ValidComputation (es.map Transformation.A) p ∧
      Smaller (inverseAs es p) (inverseComputation ss p) := by
  refine ⟨ss.map Transformation.reducedExponent, List.length_map .., ?_,
    reduced_computation_valid h, reduced_computation_smaller h⟩
  intro e he
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
  exact Transformation.reducedExponent_mem s

end Lsbgcd
