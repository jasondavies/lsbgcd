module

public import Lsbgcd.Words

@[expose] public section

/-!
# Valid partial computations (§3)

A step records the branch selected by the algorithm and whether the strict
interchange test fires. Lists are written in inverse execution order: the
first listed step is undone first. In particular, an exchanged step requires
`x > y`, as stated in the proof of Theorem 3.3; equality in the printed table
must not be interpreted as allowing an interchange.
-/
namespace Lsbgcd

inductive Transformation where
  | A (e : ℕ)
  | B (e : ℕ)
  | IA (e : ℕ)
  | IB (e : ℕ)
  deriving DecidableEq

namespace Transformation

def inverse : Transformation → ℕ × ℕ → ℕ × ℕ
  | .A e, p => inverseA e p
  | .B e, p => inverseB e p
  | .IA e, p => inverseA e (interchange p)
  | .IB e, p => inverseB e (interchange p)

/-- The algorithm selects the recorded branch, with exactly the recorded
interchange. Thus a zero second input is excluded by `ChoosesA`/`ChoosesB`. -/
def ValidOn : Transformation → ℕ × ℕ → Prop
  | .A e, p => ChoosesA e (inverseA e p).1 (inverseA e p).2 ∧ p.2 ≤ p.1
  | .B e, p => ChoosesB e (inverseB e p).1 (inverseB e p).2 ∧ p.2 ≤ p.1
  | .IA e, p =>
    ChoosesA e (inverseA e (interchange p)).1 (inverseA e (interchange p)).2 ∧ p.2 < p.1
  | .IB e, p =>
    ChoosesB e (inverseB e (interchange p)).1 (inverseB e (interchange p)).2 ∧ p.2 < p.1

theorem validA_iff (e x y : ℕ) :
    ValidOn (.A e) (x, y) ↔ 0 < x ∧ y ≤ x ∧ 2 * y ≤ 2 ^ e * x := by
  constructor
  · rintro ⟨hc, hxy⟩
    have hx : 0 < x := hc.1
    exact ⟨hx, hxy, (lemma3_1 hx).1 hc⟩
  · rintro ⟨hx, hxy, h⟩
    exact ⟨(lemma3_1 hx).2 h, hxy⟩

theorem validB_iff (e x y : ℕ) :
    ValidOn (.B e) (x, y) ↔ 0 < x ∧ y ≤ x ∧ 0 < y ∧ 2 * y < 2 ^ e * x := by
  constructor
  · rintro ⟨hc, hxy⟩
    have hx : 0 < x := hc.1
    exact ⟨hx, hxy, (lemma3_2 hx).1 hc⟩
  · rintro ⟨hx, hxy, h⟩
    exact ⟨(lemma3_2 hx).2 h, hxy⟩

private theorem exchanged_exponent {e x y : ℕ}
    (hxy : y < x) (h : 2 * x ≤ 2 ^ e * y) : 1 < e := by
  by_contra he
  have : e = 0 ∨ e = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h <;> omega

theorem validIA_iff (e x y : ℕ) :
    ValidOn (.IA e) (x, y) ↔ y < x ∧ 2 * x ≤ 2 ^ e * y ∧ 1 < e := by
  constructor
  · rintro ⟨hc, hxy⟩
    have hy : 0 < y := hc.1
    have h := (lemma3_1 hy).1 hc
    exact ⟨hxy, h, exchanged_exponent hxy h⟩
  · rintro ⟨hxy, h, _⟩
    have hy : 0 < y := by
      by_contra hn
      have hz : y = 0 := by omega
      simp [hz] at h
      omega
    exact ⟨(lemma3_1 hy).2 h, hxy⟩

theorem validIB_iff (e x y : ℕ) :
    ValidOn (.IB e) (x, y) ↔ y < x ∧ 2 * x < 2 ^ e * y ∧ 1 < e := by
  constructor
  · rintro ⟨hc, hxy⟩
    have hy : 0 < y := hc.1
    have h := ((lemma3_2 hy).1 hc).2
    exact ⟨hxy, h, exchanged_exponent hxy (le_of_lt h)⟩
  · rintro ⟨hxy, h, _⟩
    have hy : 0 < y := by
      by_contra hn
      have hz : y = 0 := by omega
      simp [hz] at h
    exact ⟨(lemma3_2 hy).2 ⟨by omega, h⟩, hxy⟩

/-- Theorem 3.3, including the strict interchange boundary. -/
theorem theorem3_3 (s : Transformation) (x y : ℕ) :
    ValidOn s (x, y) ↔ match s with
      | .A e => 0 < x ∧ y ≤ x ∧ 2 * y ≤ 2 ^ e * x
      | .B e => 0 < x ∧ y ≤ x ∧ 0 < y ∧ 2 * y < 2 ^ e * x
      | .IA e => y < x ∧ 2 * x ≤ 2 ^ e * y ∧ 1 < e
      | .IB e => y < x ∧ 2 * x < 2 ^ e * y ∧ 1 < e := by
  cases s with
  | A e => exact validA_iff e x y
  | B e => exact validB_iff e x y
  | IA e => exact validIA_iff e x y
  | IB e => exact validIB_iff e x y

theorem valid_positive_ordered {s : Transformation} {p : ℕ × ℕ}
    (h : ValidOn s p) : 0 < p.1 ∧ p.2 ≤ p.1 := by
  obtain ⟨x, y⟩ := p
  rw [theorem3_3] at h
  cases s <;> simp only at h <;> omega

/-- Validity is tied to the executable algorithm, not only to inequalities. -/
theorem valid_step {s : Transformation} {p : ℕ × ℕ} (h : ValidOn s p) :
    step (inverse s p).1 (inverse s p).2 = p := by
  obtain ⟨x, y⟩ := p
  cases s with
  | A e =>
    obtain ⟨hx, hxy, hb⟩ := (validA_iff e x y).1 h
    exact step_inverseA hx hxy hb
  | B e =>
    obtain ⟨hx, hxy, hy, hb⟩ := (validB_iff e x y).1 h
    have hs := choosesB_step h.1
    have hpow : y ≤ 2 ^ (e + 1) * x := by
      rw [pow_succ', Nat.mul_assoc]
      omega
    simpa only [inverse, inverseB, Nat.sub_sub_self hpow,
      max_eq_left hxy, min_eq_right hxy] using hs
  | IA e =>
    have hs := choosesA_step h.1
    have hxy : y ≤ x := Nat.le_of_lt h.2
    simpa only [inverse, inverseA, interchange, Nat.add_sub_cancel_left,
      max_eq_right hxy, min_eq_left hxy] using hs
  | IB e =>
    obtain ⟨hxy, hb, _⟩ := (validIB_iff e x y).1 h
    have hs := choosesB_step h.1
    have hpow : x ≤ 2 ^ (e + 1) * y := by
      rw [pow_succ', Nat.mul_assoc]
      omega
    simpa only [inverse, inverseB, interchange, Nat.sub_sub_self hpow,
      max_eq_right (Nat.le_of_lt hxy), min_eq_left (Nat.le_of_lt hxy)] using hs

end Transformation

/-- Validity of a partial computation on its output pair. -/
def ValidComputation : List Transformation → ℕ × ℕ → Prop
  | [], _ => True
  | s :: ss, p => s.ValidOn p ∧ ValidComputation ss (s.inverse p)

/-- Corollary 3.4: none of the four pairs of zero-exponent steps is valid. -/
theorem corollary3_4 (p : ℕ × ℕ) :
    ¬ ValidComputation [.A 0, .A 0] p ∧
    ¬ ValidComputation [.A 0, .B 0] p ∧
    ¬ ValidComputation [.B 0, .A 0] p ∧
    ¬ ValidComputation [.B 0, .B 0] p := by
  obtain ⟨x, y⟩ := p
  simp only [ValidComputation, and_true, Transformation.inverse,
    inverseA, inverseB, pow_zero, one_mul,
    Transformation.validA_iff, Transformation.validB_iff]
  omega

/-- No two adjacent exponents are zero. -/
def NoConsecutiveZeros : List ℕ → Prop
  | [] => True
  | [_] => True
  | e :: f :: es => (e ≠ 0 ∨ f ≠ 0) ∧ NoConsecutiveZeros (f :: es)

private theorem positive_exponent {e : ℕ} (h : e ≠ 0) : 2 ≤ 2 ^ e := by
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ e by omega)

theorem nextA_valid {e f : ℕ} {p : ℕ × ℕ}
    (h : Transformation.ValidOn (.A e) p) (hef : e ≠ 0 ∨ f ≠ 0) :
    Transformation.ValidOn (.A f) (inverseA e p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hxy, hb⟩ := (Transformation.validA_iff e x y).1 h
  rw [inverseA, Transformation.validA_iff]
  have he : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by decide)
  have hf : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by decide)
  refine ⟨by positivity, by nlinarith, ?_⟩
  rcases hef with he' | hf'
  · have := positive_exponent he'
    have hm := Nat.mul_le_mul_left (2 ^ f) (show 2 * x ≤ 2 ^ e * x + y by nlinarith)
    nlinarith
  · have := positive_exponent hf'
    have hm := Nat.mul_le_mul_left (2 ^ f) (show x ≤ 2 ^ e * x + y by nlinarith)
    nlinarith

/-- Lemma 3.5: for A-transformations without adjacent A₀ steps, validity of
the first inverse step implies validity of the whole partial computation. -/
theorem lemma3_5 {e : ℕ} {es : List ℕ} {p : ℕ × ℕ}
    (hn : NoConsecutiveZeros (e :: es)) (h : Transformation.ValidOn (.A e) p) :
    ValidComputation ((e :: es).map Transformation.A) p := by
  induction es generalizing e p with
  | nil => exact ⟨h, trivial⟩
  | cons f fs ih =>
    exact ⟨h, ih hn.2 (nextA_valid h hn.1)⟩

/-- Lemma 4.1(3), in integral form. -/
theorem inverseA_one_smaller_interchanged {e x y : ℕ}
    (hxy : y ≤ x) (h : 2 * x ≤ 2 ^ e * y) :
    Smaller (inverseA 1 (x, y)) (inverseA e (interchange (x, y))) := by
  simp only [Smaller, inverseA, interchange, pow_one]
  omega

end Lsbgcd
