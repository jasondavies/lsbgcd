import Lsbgcd.Algorithm

/-!
# Transformations and their domains (§§2–4)

The inequalities are multiplied by two to avoid the paper's `2^(e-1)`
at `e = 0`. Transformations act before the possible interchange.
-/
namespace Lsbgcd

def inverseA (e : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 ^ e * p.1 + p.2, p.1)
def inverseB (e : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 ^ (e + 1) * p.1 - p.2, p.1)
def interchange (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

def ChoosesA (e u v : ℕ) : Prop :=
  0 < v ∧ 2 ^ e * v ≤ u ∧ u < 2 ^ (e + 1) * v ∧
    u - 2 ^ e * v ≤ 2 ^ (e + 1) * v - u

def ChoosesB (e u v : ℕ) : Prop :=
  0 < v ∧ 2 ^ e * v ≤ u ∧ u < 2 ^ (e + 1) * v ∧
    2 ^ (e + 1) * v - u < u - 2 ^ e * v

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

theorem smaller_trans {p q r : ℕ × ℕ} (hpq : Smaller p q) (hqr : Smaller q r) :
    Smaller p r := ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

def LexLE (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

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
