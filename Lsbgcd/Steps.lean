module

public import Lsbgcd.Algorithm

@[expose] public section

/-!
# Transformations and their domains (§§2–4)

The inequalities are multiplied by two to avoid the paper's `2^(e-1)`
at `e = 0`. Transformations act before the possible interchange.
-/
namespace Lsbgcd

/-- Undo an A-step with exponent `e`: the input `(2^e x + y, x)` whose
remainder `u − 2^e v` is `y`. -/
def inverseA (e : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 ^ e * p.1 + p.2, p.1)
/-- Undo a B-step with exponent `e`: the input `(2^(e+1) x − y, x)` whose
remainder `2^(e+1) v − u` is `y`. -/
def inverseB (e : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 ^ (e + 1) * p.1 - p.2, p.1)
/-- Swap the two coordinates. -/
def interchange (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

/-- On input `(u, v)`, the loop selects exponent `e` and takes branch A
(subtracting `2^e v`); ties go to A. -/
def ChoosesA (e u v : ℕ) : Prop :=
  0 < v ∧ 2 ^ e * v ≤ u ∧ u < 2 ^ (e + 1) * v ∧
    u - 2 ^ e * v ≤ 2 ^ (e + 1) * v - u

/-- On input `(u, v)`, the loop selects exponent `e` and takes branch B
(subtracting from `2^(e+1) v`). -/
def ChoosesB (e u v : ℕ) : Prop :=
  0 < v ∧ 2 ^ e * v ≤ u ∧ u < 2 ^ (e + 1) * v ∧
    2 ^ (e + 1) * v - u < u - 2 ^ e * v

theorem choosesA_ordered {e u v : ℕ} (h : ChoosesA e u v) : 0 < v ∧ v ≤ u := by
  obtain ⟨hv, hl, -, -⟩ := h
  have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  exact ⟨hv, by nlinarith⟩

theorem choosesB_ordered {e u v : ℕ} (h : ChoosesB e u v) : 0 < v ∧ v ≤ u := by
  obtain ⟨hv, hl, -, -⟩ := h
  have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  exact ⟨hv, by nlinarith⟩

theorem shift_eq {e u v : ℕ} (hv : 0 < v)
    (hl : 2 ^ e * v ≤ u) (hu : u < 2 ^ (e + 1) * v) : shift u v = e := by
  unfold shift
  have hq : u / v ≠ 0 := by
    have h := (Nat.le_div_iff_mul_le hv).2 hl
    have : 0 < 2 ^ e := by positivity
    omega
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, hq⟩)).2
    ⟨(Nat.le_div_iff_mul_le hv).2 hl, (Nat.div_lt_iff_lt_mul hv).2 hu⟩

/-- Lemma 3.1, with the necessary nonterminal hypothesis explicit. -/
theorem lemma3_1 {e x y : ℕ} (hx : 0 < x) :
    ChoosesA e (inverseA e (x, y)).1 (inverseA e (x, y)).2 ↔
      2 * y ≤ 2 ^ e * x := by
  have hp : 0 < 2 ^ e * x := Nat.mul_pos (by positivity) hx
  simp only [ChoosesA, inverseA, pow_succ', Nat.mul_assoc]
  constructor
  · rintro ⟨_, _, hu, ht⟩
    omega
  · intro h
    refine ⟨hx, by omega, ?_, ?_⟩ <;> omega

/-- Lemma 3.2. Strict comparison excludes both zero remainder and ties. -/
theorem lemma3_2 {e x y : ℕ} (hx : 0 < x) :
    ChoosesB e (inverseB e (x, y)).1 (inverseB e (x, y)).2 ↔
      0 < y ∧ 2 * y < 2 ^ e * x := by
  have hp : 0 < 2 ^ e * x := Nat.mul_pos (by positivity) hx
  simp only [ChoosesB, inverseB, pow_succ', Nat.mul_assoc]
  constructor
  · rintro ⟨_, hl, hu, ht⟩
    omega
  · rintro ⟨hy, h⟩
    refine ⟨hx, ?_, ?_, ?_⟩ <;> omega

theorem choosesA_step {e u v : ℕ} (h : ChoosesA e u v) :
    step u v = (max v (u - 2 ^ e * v), min v (u - 2 ^ e * v)) := by
  obtain ⟨hv, hl, hu, ht⟩ := h
  simp [step, remainder, shift_eq hv hl hu, min_eq_left ht]

theorem choosesB_step {e u v : ℕ} (h : ChoosesB e u v) :
    step u v = (max v (2 ^ (e + 1) * v - u),
      min v (2 ^ (e + 1) * v - u)) := by
  obtain ⟨hv, hl, hu, ht⟩ := h
  simp [step, remainder, shift_eq hv hl hu, min_eq_right (le_of_lt ht)]

/-- The order used in §4: compare first coordinates and coordinate sums. -/
def Smaller (p q : ℕ × ℕ) : Prop := p.1 ≤ q.1 ∧ p.1 + p.2 ≤ q.1 + q.2

theorem smaller_refl (p : ℕ × ℕ) : Smaller p p := ⟨le_rfl, le_rfl⟩

theorem smaller_trans {p q r : ℕ × ℕ} (hpq : Smaller p q) (hqr : Smaller q r) :
    Smaller p r := ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

/-- Lexicographic order on pairs: first coordinates, then second coordinates. -/
def LexLE (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

theorem lexLE_trans {p q r : ℕ × ℕ} (hpq : LexLE p q) (hqr : LexLE q r) :
    LexLE p r := by
  unfold LexLE at *
  omega

theorem smaller_lex {p q : ℕ × ℕ} (h : Smaller p q) : LexLE p q := by
  unfold Smaller at h
  unfold LexLE
  omega

/-- Lemma 4.1(1). -/
theorem inverseA_smaller_inverseB {e x y : ℕ} (h : 2 * y ≤ 2 ^ e * x) :
    Smaller (inverseA e (x, y)) (inverseB e (x, y)) := by
  simp only [Smaller, inverseA, inverseB, pow_succ', Nat.mul_assoc]
  omega

/-- Lemma 4.1(2). -/
theorem inverseA_mono_exponent {e f x y : ℕ} (h : e ≤ f) :
    Smaller (inverseA e (x, y)) (inverseA f (x, y)) := by
  have hp := Nat.mul_le_mul_right x (Nat.pow_le_pow_right (by decide : 0 < 2) h)
  simp only [Smaller, inverseA]
  omega

/-- One-step version of Lemma 4.2. -/
theorem inverseA_mono {p q : ℕ × ℕ} (e : ℕ) (h : Smaller p q) :
    Smaller (inverseA e p) (inverseA e q) := by
  have hp : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by decide)
  obtain ⟨h1, h2⟩ := h
  simp only [Smaller, inverseA]
  constructor <;> nlinarith

/-- An inverse partial computation, in the paper's composition order. -/
def inverseAs : List ℕ → ℕ × ℕ → ℕ × ℕ
  | [], p => p
  | e :: es, p => inverseAs es (inverseA e p)

/-- Lemma 4.2 for arbitrary lists of A-transformations. -/
theorem lemma4_2 {p q : ℕ × ℕ} (es : List ℕ) (h : Smaller p q) :
    Smaller (inverseAs es p) (inverseAs es q) := by
  induction es generalizing p q with
  | nil => exact h
  | cons e es ih => exact ih (inverseA_mono e h)

end Lsbgcd
