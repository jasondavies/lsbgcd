module

public import Lsbgcd.Ramharter

@[expose] public section

/-! # Structural equations for the general Ramharter arrangement -/
namespace Lsbgcd

/-- Shifting every rank commutes with the recursive rank arrangement. -/
theorem ramharterIndices_add (lo n k : ℕ) :
    (ramharterIndices lo n).map (fun i => i + k) = ramharterIndices (lo + k) n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · rfl
    · rfl
    · simp [ramharterIndices, Nat.add_assoc, Nat.add_comm]
    · simp [ramharterIndices, Nat.add_assoc, Nat.add_comm]
    · simp only [ramharterIndices, List.map_append, List.map_cons, List.map_nil,
        ih n (by omega)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem ramharterWord_nil : ramharterWord [] = [] := rfl

@[simp] theorem ramharterWord_singleton (a : ℕ) : ramharterWord [a] = [a] := by
  simp [ramharterWord, ramharterIndices]

@[simp] theorem ramharterWord_pair (a b : ℕ) : ramharterWord [a, b] = [a, b] := by
  simp [ramharterWord, ramharterIndices]

@[simp] theorem ramharterWord_triple (a b c : ℕ) :
    ramharterWord [a, b, c] = [a, c, b] := by
  simp [ramharterWord, ramharterIndices]

/-- Remove the two least and two greatest ranks. This equation holds for
every digit list; ordering is needed only when proving extremality. -/
theorem ramharterWord_strip_four (a b : ℕ) (bs : List ℕ) (c d : ℕ) :
    ramharterWord (a :: b :: (bs ++ [c, d])) =
      [a, d] ++ ramharterWord bs ++ [c, b] := by
  have hshift : (ramharterIndices 0 bs.length).map (fun i => i + 2) =
      ramharterIndices 2 bs.length := by
    simpa using ramharterIndices_add 0 bs.length 2
  have hmiddle : (ramharterIndices 2 bs.length).map
      (fun i => (a :: b :: (bs ++ [c, d])).getD i 0) = ramharterWord bs := by
    rw [← hshift, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hb := (ramharterIndices_bounds hi).2
    simp only [Function.comp_apply, List.getD_cons_succ]
    exact List.getD_append _ _ _ _ (by simpa using hb)
  have hc : (bs ++ [c, d]).getD bs.length 0 = c := by
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  have hd : (bs ++ [c, d]).getD (bs.length + 1) 0 = d := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hlen : (a :: b :: (bs ++ [c, d])).length = bs.length + 4 := by simp
  rw [ramharterWord, hlen]
  simp only [ramharterIndices, zero_add, List.map_append, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, hmiddle, hc, hd]
  rfl

/-- An equivalent two-endpoint recursion. Reversing the remaining sorted
list exchanges the roles of its least and greatest entries at each layer. -/
theorem ramharterWord_two (a b : ℕ) (rest : List ℕ) :
    ramharterWord (a :: b :: rest) = a :: (ramharterWord rest.reverse ++ [b]) := by
  generalize hn : rest.length = n
  induction n using Nat.strong_induction_on generalizing a b rest with
  | h n ih =>
    cases hr : rest.reverse with
    | nil =>
      have he : rest = [] := by simpa using congrArg List.reverse hr
      subst rest
      simp
    | cons d ds =>
      cases ds with
      | nil =>
        have he : rest = [d] := by simpa using congrArg List.reverse hr
        subst rest
        simp
      | cons c cs =>
        have he : rest = cs.reverse ++ [c, d] := by
          simpa [List.append_assoc] using congrArg List.reverse hr
        have hlen : cs.length < n := by
          have hh := congrArg List.length hr
          simp only [List.length_reverse, List.length_cons] at hh
          omega
        have hi := ih cs.length hlen d c cs rfl
        rw [he, ramharterWord_strip_four, hi]
        simp [List.append_assoc]

end Lsbgcd
