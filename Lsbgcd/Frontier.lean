import Lsbgcd.Candidates

/-!
# A finite family dominating all admissible words

Odd lengths are dominated in the §4 order by the alternating word.
Even lengths are dominated by a word `(12)^i (21)^j` of the same length.
This gives a direct binary-continuant reduction without assuming Ramharter.
-/
namespace Lsbgcd

theorem smaller_refl (p : ℕ × ℕ) : Smaller p p := ⟨le_rfl, le_rfl⟩

theorem repeat21_add (i j : ℕ) : repeat21 (i + j) = repeat21 i ++ repeat21 j := by
  induction i with
  | zero => simp [repeat21]
  | succ i ih => simpa [repeat21, Nat.succ_add] using congrArg (fun as => 2 :: 1 :: as) ih

theorem two_repeat12 (n : ℕ) (as : List ℕ) :
    (2 :: repeat12 n) ++ as = repeat21 n ++ 2 :: as := by
  induction n with
  | zero => simp [repeat12, repeat21]
  | succ n ih => simpa [repeat12, repeat21] using congrArg (fun as => 2 :: 1 :: as) ih

theorem repeat12_one (n : ℕ) : repeat12 n ++ [1] = 1 :: repeat21 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeat12, repeat21, ih]

private def frontierCoeff : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let p := frontierCoeff n
    (3 * p.1 + p.2, 2 * p.1 + p.2)

private theorem repeat21_convergent (n : ℕ) (as : List ℕ) :
    convergent (repeat21 n ++ as) =
      ((2 * (frontierCoeff n).1 + (frontierCoeff n).2) * (convergent as).1 +
        2 * (frontierCoeff n).1 * (convergent as).2,
       (frontierCoeff n).1 * (convergent as).1 +
        (frontierCoeff n).2 * (convergent as).2) := by
  induction n with
  | zero => simp [repeat21, frontierCoeff]
  | succ n ih =>
    simp only [repeat21, List.cons_append, convergent, frontierCoeff, ih]
    congr 1 <;> ring

private theorem move_two (n : ℕ) (as : List ℕ)
    (h : (convergent as).2 ≤ (convergent as).1) :
    Smaller (convergent (1 :: (repeat21 n ++ as)))
      (convergent (repeat21 n ++ (2 :: as))) := by
  rw [repeat21_convergent]
  simp only [convergent, repeat21_convergent, Smaller]
  constructor <;> nlinarith [Nat.mul_le_mul_left (frontierCoeff n).1 h]

private theorem frontierCoeff_pos (n : ℕ) : 0 < (frontierCoeff n).2 := by
  induction n with
  | zero => decide
  | succ n ih => simp only [frontierCoeff]; omega

private theorem move_two_strict (n : ℕ) (as : List ℕ)
    (h : 0 < (convergent as).1) :
    (convergent (1 :: (repeat21 n ++ as))).1 <
      (convergent (repeat21 n ++ (2 :: as))).1 := by
  rw [repeat21_convergent]
  simp only [convergent, repeat21_convergent]
  have hp := Nat.mul_pos (frontierCoeff_pos n) h
  nlinarith

/-- The alternating odd word dominates any word `2 (12)^i (21)^j`. -/
theorem odd_dominates_two_family (i j : ℕ) :
    Smaller (convergent (repeat12 (i + j) ++ [1]))
      (convergent (2 :: (repeat12 i ++ repeat21 j))) := by
  have h := (admissible_convergent (admissible_repeat21 j)).2
  have hm := move_two i (repeat21 j) h
  rw [repeat12_one, repeat21_add]
  have hw : 2 :: (repeat12 i ++ repeat21 j) = repeat21 i ++ 2 :: repeat21 j :=
    two_repeat12 i (repeat21 j)
  rw [hw]
  exact hm

theorem odd_dominates_two_family_strict (i j : ℕ) :
    (convergent (repeat12 (i + j) ++ [1])).1 <
      (convergent (2 :: (repeat12 i ++ repeat21 j))).1 := by
  have h := (admissible_convergent (admissible_repeat21 j)).1
  have hm := move_two_strict i (repeat21 j) h
  rw [repeat12_one, repeat21_add]
  have hw : 2 :: (repeat12 i ++ repeat21 j) = repeat21 i ++ 2 :: repeat21 j :=
    two_repeat12 i (repeat21 j)
  rw [hw]
  exact hm

private theorem prefix_two_smaller {as bs : List ℕ}
    (h : Smaller (convergent as) (convergent bs)) :
    Smaller (convergent (2 :: as)) (convergent (2 :: bs)) := by
  simpa [inverseA, convergent] using inverseA_mono 1 h

private theorem prefix_twelve_smaller {as bs : List ℕ}
    (h : Smaller (convergent as) (convergent bs)) :
    Smaller (convergent (1 :: 2 :: as)) (convergent (1 :: 2 :: bs)) := by
  simpa [inverseA, convergent] using inverseA_mono 0 (inverseA_mono 1 h)

/-- An odd alternating word or an even split word dominates every
admissible word, with exactly the same number of digits. -/
theorem admissible_frontier (as : List ℕ) (h : Admissible as) :
    (∃ k, as.length = 2 * k + 1 ∧
      Smaller (convergent (repeat12 k ++ [1])) (convergent as)) ∨
    (∃ i j, as.length = 2 * (i + j) ∧
      Smaller (convergent (repeat12 i ++ repeat21 j)) (convergent as)) := by
  cases as with
  | nil => exact Or.inr ⟨0, 0, rfl, smaller_refl _⟩
  | cons a as =>
    obtain ha | ha := admissible_head h
    · subst a
      cases as with
      | nil => exact Or.inl ⟨0, rfl, smaller_refl _⟩
      | cons b bs =>
        have hb := admissible_head (admissible_tail h)
        have hn : ¬(1 = 1 ∧ b = 1) := h.2.1
        have hb2 : b = 2 := by omega
        subst b
        have ht := admissible_tail (admissible_tail h)
        rcases admissible_frontier bs ht with ⟨k, hk, hs⟩ | ⟨i, j, hij, hs⟩
        · refine Or.inl ⟨k + 1, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · exact prefix_twelve_smaller hs
        · refine Or.inr ⟨i + 1, j, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · exact prefix_twelve_smaller hs
    · subst a
      have ht := admissible_tail h
      rcases admissible_frontier as ht with ⟨k, hk, hs⟩ | ⟨i, j, hij, hs⟩
      · refine Or.inr ⟨0, k + 1, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · have hm := prefix_two_smaller hs
          simpa [repeat12_one, repeat12, repeat21] using hm
      · refine Or.inl ⟨i + j, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · exact smaller_trans (odd_dominates_two_family i j) (prefix_two_smaller hs)
termination_by as.length

private theorem first_eq_of_two {as bs : List ℕ}
    (h : Smaller (convergent as) (convergent bs))
    (he : (convergent (2 :: as)).1 = (convergent (2 :: bs)).1) :
    (convergent as).1 = (convergent bs).1 := by
  obtain ⟨h1, h2⟩ := h
  simp only [convergent] at he
  omega

private theorem first_eq_of_twelve {as bs : List ℕ}
    (h : Smaller (convergent as) (convergent bs))
    (he : (convergent (1 :: 2 :: as)).1 = (convergent (1 :: 2 :: bs)).1) :
    (convergent as).1 = (convergent bs).1 := by
  obtain ⟨h1, h2⟩ := h
  simp only [convergent] at he
  omega

/-- Equality in the numerator forces the word itself to be one of the
dominating words. This retains the uniqueness information needed in §5. -/
theorem admissible_frontier_eq (as : List ℕ) (h : Admissible as) :
    (∃ k, as.length = 2 * k + 1 ∧
      Smaller (convergent (repeat12 k ++ [1])) (convergent as) ∧
      ((convergent (repeat12 k ++ [1])).1 = (convergent as).1 →
        as = repeat12 k ++ [1])) ∨
    (∃ i j, as.length = 2 * (i + j) ∧
      Smaller (convergent (repeat12 i ++ repeat21 j)) (convergent as) ∧
      ((convergent (repeat12 i ++ repeat21 j)).1 = (convergent as).1 →
        as = repeat12 i ++ repeat21 j)) := by
  cases as with
  | nil => exact Or.inr ⟨0, 0, rfl, smaller_refl _, fun _ => rfl⟩
  | cons a as =>
    obtain ha | ha := admissible_head h
    · subst a
      cases as with
      | nil => exact Or.inl ⟨0, rfl, smaller_refl _, fun _ => rfl⟩
      | cons b bs =>
        have hb := admissible_head (admissible_tail h)
        have hn : ¬(1 = 1 ∧ b = 1) := h.2.1
        have hb2 : b = 2 := by omega
        subst b
        have ht := admissible_tail (admissible_tail h)
        rcases admissible_frontier_eq bs ht with ⟨k, hk, hs, he⟩ | ⟨i, j, hij, hs, he⟩
        · refine Or.inl ⟨k + 1, ?_, prefix_twelve_smaller hs, ?_⟩
          · simp only [List.length_cons]; omega
          · intro heq
            have hw := he (first_eq_of_twelve hs heq)
            simp [repeat12, hw]
        · refine Or.inr ⟨i + 1, j, ?_, prefix_twelve_smaller hs, ?_⟩
          · simp only [List.length_cons]; omega
          · intro heq
            have hw := he (first_eq_of_twelve hs heq)
            simp [repeat12, hw]
    · subst a
      have ht := admissible_tail h
      rcases admissible_frontier_eq as ht with ⟨k, hk, hs, he⟩ | ⟨i, j, hij, hs, _⟩
      · refine Or.inr ⟨0, k + 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · simpa [repeat12_one, repeat12, repeat21] using prefix_two_smaller hs
        · intro heq
          have heq' : (convergent (2 :: (repeat12 k ++ [1]))).1 =
              (convergent (2 :: as)).1 := by
            simpa [repeat12_one, repeat12, repeat21] using heq
          have hw := he (first_eq_of_two hs heq')
          simp [hw, repeat12_one, repeat12, repeat21]
      · refine Or.inl ⟨i + j, ?_,
          smaller_trans (odd_dominates_two_family i j) (prefix_two_smaller hs), ?_⟩
        · simp only [List.length_cons]; omega
        · intro heq
          have hl := odd_dominates_two_family_strict i j
          have hu := (prefix_two_smaller hs).1
          omega
termination_by as.length

end Lsbgcd
