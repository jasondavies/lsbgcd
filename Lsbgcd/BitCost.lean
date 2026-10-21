module

public import Lsbgcd.BinaryImplementation

@[expose] public section

/-!
# Binary primitive cost accounting

This module uses the usual bit-scan cost model: a length scan or copy costs
the operand width, comparison and subtraction cost the larger operand width,
and materialising a left shift costs the output width. These charges are
specified explicitly below; they are not the running time of Lean's `Nat`
implementation or a claim about a particular machine.

`binaryLoopTrace` lists the operations of the binary-length implementation,
including the zero test, both remainder subtractions, selection and copies.
It eagerly charges the exponent adjustment and recomputes the selected shift,
so the same trace bound applies to either comparison branch. `binaryCost`
sums these traces along the execution of `binaryStep`, which agrees with the
specified `step` by `binaryStep_eq_step`. The accumulated cost is bounded by
a constant times the square of the initial bit width.
-/
namespace Lsbgcd

/-- Binary storage width, using the one-bit representation `0` for zero. -/
def bitWidth (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The primitive operations of the binary implementation, recorded with the
operands that determine their cost. -/
inductive BitPrimitive where
  | scan (x : ℕ)
  | compare (x y : ℕ)
  | subtract (x y : ℕ)
  | leftShift (x k : ℕ)
  | copy (x : ℕ)

/-- The charge for one primitive in the bit-scan model described above. -/
def BitPrimitive.cost : BitPrimitive → ℕ
  | .scan x | .copy x => bitWidth x
  | .compare x y | .subtract x y => max (bitWidth x) (bitWidth y)
  | .leftShift x k => bitWidth x + k

/-- The bit primitives in one loop iteration of `binaryStep`. -/
def binaryLoopTrace (u v : ℕ) : List BitPrimitive :=
  let k := lengthShift u v
  let w := 2 ^ k * v
  let e := shiftByLengths u v
  let a := 2 ^ e * v
  let b := 2 ^ (e + 1) * v
  let l := u - a
  let r := b - u
  let t := min l r
  [.compare v 0, .scan u, .scan v,
   .subtract (Nat.log 2 u) (Nat.log 2 v),
   .leftShift v k, .compare w u, .subtract k 1,
   .leftShift v e, .leftShift a 1,
   .subtract u a, .subtract b u,
   .compare l r, .compare v t, .copy v, .copy t]

/-- The total charge for one loop iteration on `(u, v)`. -/
def binaryLoopCost (u v : ℕ) : ℕ :=
  ((binaryLoopTrace u v).map BitPrimitive.cost).sum

private theorem bitWidth_mono {m n : ℕ} (h : m ≤ n) : bitWidth m ≤ bitWidth n := by
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bitWidth_double {u : ℕ} (hu : 0 < u) :
    bitWidth (2 * u) = bitWidth u + 1 := by
  simp only [bitWidth, Nat.mul_comm 2, Nat.log_mul_base (by decide : 1 < 2) (ne_of_gt hu)]

/-- Every primitive in a loop acts on at most one more than the input width,
so each costs at most `2 * bitWidth u`. The trace has fifteen primitives,
which gives the constant `30`. -/
theorem binaryLoopCost_le {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    binaryLoopCost u v ≤ 30 * bitWidth u := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hW : 1 ≤ bitWidth u := by unfold bitWidth; omega
  have hvW := bitWidth_mono hvu
  have hzW := bitWidth_mono (Nat.zero_le u)
  have hoW : bitWidth 1 ≤ bitWidth u := bitWidth_mono (by omega)
  have hluW := bitWidth_mono (Nat.log_le_self 2 u)
  have hlvW := bitWidth_mono ((Nat.log_le_self 2 v).trans hvu)
  have hk : lengthShift u v ≤ Nat.log 2 u := Nat.sub_le _ _
  have hkW := bitWidth_mono (hk.trans (Nat.log_le_self 2 u))
  have hlogs : Nat.log 2 v ≤ Nat.log 2 u := Nat.log_mono_right hvu
  have hshiftW : bitWidth v + lengthShift u v = bitWidth u := by
    unfold bitWidth lengthShift
    omega
  have he : shiftByLengths u v ≤ lengthShift u v := by
    unfold shiftByLengths
    dsimp only
    split_ifs <;> omega
  obtain ⟨hal, hbu⟩ := shiftByLengths_bounds hv hvu
  have hb : 2 ^ (shiftByLengths u v + 1) * v ≤ 2 * u := by
    rw [pow_succ]
    nlinarith
  have hw : 2 ^ lengthShift u v * v ≤ 2 * u :=
    le_of_lt (lengthShift_approximates hv hvu).1
  have haW := bitWidth_mono hal
  have hbW := bitWidth_mono hb
  have hwW := bitWidth_mono hw
  rw [bitWidth_double hu] at hbW hwW
  have hlW := bitWidth_mono (Nat.sub_le u (2 ^ shiftByLengths u v * v))
  have hr : 2 ^ (shiftByLengths u v + 1) * v - u ≤ u := by omega
  have hrW := bitWidth_mono hr
  have htW := bitWidth_mono ((min_le_left
    (u - 2 ^ shiftByLengths u v * v) (2 ^ (shiftByLengths u v + 1) * v - u)).trans
      (Nat.sub_le _ _))
  have hcost : ∀ op ∈ binaryLoopTrace u v, op.cost ≤ 2 * bitWidth u := by
    simp only [binaryLoopTrace, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, BitPrimitive.cost]
    constructorm* _ ∧ _ <;> omega
  calc
    binaryLoopCost u v ≤ ((binaryLoopTrace u v).map (fun _ => 2 * bitWidth u)).sum :=
      List.sum_le_sum hcost
    _ = 30 * bitWidth u := by simp [binaryLoopTrace]; omega

/-- Cost of the complete algorithm in the stated primitive model, including
the terminal zero test and copying the returned result. -/
def binaryCost (u v : ℕ) (_hvu : v ≤ u) : ℕ :=
  if _hv : v = 0 then bitWidth v + bitWidth u
  else binaryLoopCost u v +
    binaryCost (binaryStep u v).1 (binaryStep u v).2 (binaryStep_ordered u v)
termination_by u + v
decreasing_by
  rw [binaryStep_eq_step (Nat.pos_of_ne_zero _hv) _hvu]
  exact step_decreases (Nat.pos_of_ne_zero _hv) _hvu

private theorem step_first_le {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    (step u v).1 ≤ u :=
  max_le hvu (le_of_lt (remainder_lt hv hvu))

/-- Summing the primitive charges over the verified execution. -/
theorem binaryCost_le_iterations (u v : ℕ) (hvu : v ≤ u) :
    binaryCost u v hvu ≤ 30 * bitWidth u * ((run u v hvu).2 + 1) := by
  rw [binaryCost, run]
  split_ifs with hv
  · subst v
    simp only [bitWidth, Nat.log_zero_right, zero_add, Nat.mul_one]
    omega
  · have hvp := Nat.pos_of_ne_zero hv
    have hc := binaryLoopCost_le hvp hvu
    have ih := binaryCost_le_iterations (binaryStep u v).1 (binaryStep u v).2
      (binaryStep_ordered u v)
    simp only [binaryStep_eq_step hvp hvu] at ih ⊢
    have hw := bitWidth_mono (step_first_le hvp hvu)
    nlinarith
termination_by u + v
decreasing_by
  rw [binaryStep_eq_step (Nat.pos_of_ne_zero hv) hvu]
  exact step_decreases (Nat.pos_of_ne_zero hv) hvu

/-- A simple width bound suffices for the quadratic cost estimate. -/
theorem iterations_le_twice_width {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    iterations u v ≤ 2 * bitWidth u + 1 := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hup : u ≤ 2 ^ bitWidth u := le_of_lt (Nat.lt_pow_succ_log_self (by decide) u)
  have hvp : v ≤ 2 ^ bitWidth u := hvu.trans hup
  have hp : u * v ≤ 2 ^ (2 * bitWidth u) := by
    have := Nat.mul_le_mul hup hvp
    simpa only [two_mul, pow_add] using this
  have hlog := Nat.log_mono_right (b := 2) hp
  rw [Nat.log_pow (by decide)] at hlog
  have hbase := Nat.log_mono (m := u * v) (n := u * v) (b := 3) (c := 2)
    (by decide) (by decide) le_rfl
  have hn := iterations_le_log_product hv hvu
  omega

/-- The paper's quadratic binary-cost bound in the explicit bit-scan model.
The constant is deliberately loose: `30 * W * (2 * W + 2) ≤ 120 * W ^ 2` for
the width `W ≥ 1`. The logarithmic order is the conclusion. -/
theorem binaryCost_quadratic {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    binaryCost u v hvu ≤ 120 * bitWidth u ^ 2 := by
  have hc := binaryCost_le_iterations u v hvu
  rw [← iterations_of_ordered hvu] at hc
  have hn := iterations_le_twice_width hv hvu
  have hW : 1 ≤ bitWidth u := by unfold bitWidth; omega
  nlinarith

/-- The input-product version of p. 474's quadratic logarithmic bound. -/
theorem binaryCost_product_quadratic {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) :
    binaryCost u v hvu ≤ 120 * (Nat.log 2 (u * v) + 1) ^ 2 := by
  have hp : u ≤ u * v := by nlinarith
  have hw := bitWidth_mono hp
  have hc := binaryCost_quadratic hv hvu
  unfold bitWidth at hw hc
  nlinarith

end Lsbgcd
