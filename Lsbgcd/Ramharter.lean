module

public import Lsbgcd.Continuants

@[expose] public section

/-!
# The general permutation theorem quoted as Theorem 5.1

The theorem in the paper concerns every multiset of positive integer digits,
not only the admissible binary words used by the GCD analysis. Its full
statement is recorded below and proved in `RamharterSort.lean`, whose header
maps out the supporting modules. The specialised binary result is also proved
independently in `Minimality.lean`.

The displayed three-case permutation is represented by stripping four ranks
at a time: the two least and the two greatest remaining entries are placed
at the two ends. Inputs with at most three entries are the base cases.
-/
namespace Lsbgcd

/-- `ramharterIndices lo n` arranges the `n` ranks `lo, …, hi`, where
`hi = lo + n − 1`, in the minimising order. For `n ≥ 4` it is
`lo, hi, (ramharterIndices (lo + 2) (n − 4)), hi − 1, lo + 1`; that is, the two
least and two greatest remaining ranks are placed at the ends and the rule
recurses inward. This recursion gives all three cases of the paper's displayed
formula for Theorem 5.1. -/
def ramharterIndices (lo : ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => [lo]
  | 2 => [lo, lo + 1]
  | 3 => [lo, lo + 2, lo + 1]
  | n + 4 => lo :: (lo + n + 3) :: ramharterIndices (lo + 2) n ++
      [lo + n + 2, lo + 1]

/-- Apply the rank arrangement to a sorted list. The use of `getD` makes
this a total definition; every rank is less than `bs.length`, so the default
is never used (see `ramharterIndices_bounds`). -/
def ramharterWord (bs : List ℕ) : List ℕ :=
  (ramharterIndices 0 bs.length).map (fun i => bs.getD i 0)

@[simp] theorem ramharterIndices_length (lo n : ℕ) :
    (ramharterIndices lo n).length = n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [ramharterIndices, List.length_cons, List.length_append,
        List.length_nil]
      rw [ih n (by omega)]

/-- Every rank lies in the interval that it rearranges. -/
theorem ramharterIndices_bounds {lo n i : ℕ} (hi : i ∈ ramharterIndices lo n) :
    lo ≤ i ∧ i < lo + n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · simp [ramharterIndices] at hi
    · simp only [ramharterIndices, List.mem_singleton] at hi
      omega
    · simp only [ramharterIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    · simp only [ramharterIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    · simp only [ramharterIndices, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hi
      rcases hi with (hi | hi | hi) | hi | hi
      · omega
      · omega
      · have hb := ih n (by omega) hi
        omega
      · omega
      · omega

/-- The rank arrangement is a permutation, including when values repeat. -/
theorem ramharterIndices_perm (lo n : ℕ) :
    (ramharterIndices lo n).Perm (List.range' lo n) := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · simp [ramharterIndices]
    · simp [ramharterIndices, List.range'_succ]
    · simp [ramharterIndices, List.range'_succ]
    · apply List.perm_iff_count.mpr
      intro a
      simp only [ramharterIndices, List.range'_succ, List.range'_zero,
        List.count_cons, List.count_nil]
      have he : lo + 1 + 1 = lo + 2 := by omega
      rw [he]
      omega
    · apply List.perm_iff_count.mpr
      intro a
      have hh := List.perm_iff_count.mp (ih n (by omega) (lo + 2)) a
      have hr : List.range' lo (n + 1 + 1 + 1 + 1) =
          (lo :: (lo + 1) :: List.range' (lo + 2) n) ++ [lo + n + 2, lo + n + 3] := by
        rw [List.range'_concat, List.range'_concat,
          List.range'_succ, List.range'_succ]
        simp only [List.cons_append, List.append_assoc, one_mul]
        rfl
      rw [hr]
      simp only [ramharterIndices, List.count_append, List.count_cons, List.count_nil]
      rw [hh]
      omega

@[simp] theorem ramharterWord_length (bs : List ℕ) :
    (ramharterWord bs).length = bs.length := by
  simp [ramharterWord]

private theorem map_getD_range (bs : List ℕ) :
    (List.range bs.length).map (fun i => bs.getD i 0) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def]
    exact ih

/-- The displayed arrangement preserves the multiset of actual digits. -/
theorem ramharterWord_perm (bs : List ℕ) : (ramharterWord bs).Perm bs := by
  have h := (ramharterIndices_perm 0 bs.length).map (fun i => bs.getD i 0)
  rw [List.range'_eq_map_range] at h
  simp only [zero_add] at h
  have hm : List.map (fun x : ℕ => x) (List.range bs.length) = List.range bs.length := by simp
  rw [hm, map_getD_range] at h
  exact h

/-- Global minimality over all permutations of a fixed multiset. -/
def IsPermutationMinimum (bs cs : List ℕ) : Prop :=
  cs.Perm bs ∧ ∀ as, as.Perm bs → continuant cs ≤ continuant as

/-- The full general statement of Theorem 5.1, including repeated entries
and uniqueness of the digit word up to reversal. The theorem is proved as
`ramharter_theorem` in `RamharterSort.lean`. -/
def RamharterTheorem : Prop :=
  ∀ bs : List ℕ, (∀ b ∈ bs, 0 < b) → bs.Pairwise (· ≤ ·) →
    IsPermutationMinimum bs (ramharterWord bs) ∧
    ∀ as, as.Perm bs →
      (continuant as = continuant (ramharterWord bs) ↔
        as = ramharterWord bs ∨ as = (ramharterWord bs).reverse)

/-- Reversing an interval factors the change in the continuant into one
factor from the interval and another from the two surrounding words. This
is the exchange identity underlying the general permutation argument. -/
theorem continuant_reverse_interval_difference (as bs cs : List ℕ) :
    (continuant (as ++ bs ++ cs) : ℤ) - continuant (as ++ bs.reverse ++ cs) =
      (wordMatrix bs 0 1 - wordMatrix bs 1 0) *
        (wordMatrix as 0 0 * wordMatrix cs 1 0 -
          wordMatrix as 0 1 * wordMatrix cs 0 0) := by
  have h1 := (wordMatrix_first_column (as ++ bs ++ cs)).1
  have h2 := (wordMatrix_first_column (as ++ bs.reverse ++ cs)).1
  change wordMatrix (as ++ bs ++ cs) 0 0 = (continuant (as ++ bs ++ cs) : ℤ) at h1
  change wordMatrix (as ++ bs.reverse ++ cs) 0 0 =
    (continuant (as ++ bs.reverse ++ cs) : ℤ) at h2
  rw [← h1, ← h2]
  simp only [wordMatrix_append, wordMatrix_reverse, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.transpose_apply]
  ring

end Lsbgcd
