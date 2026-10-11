import Lsbgcd.Candidates

/-! # Kernel-checked examples from the paper -/
namespace Lsbgcd

/-- The full sequence of transitions in the example on p. 476. -/
theorem paper_trace :
    [step 47 40, step 40 7, step 12 7, step 7 2, step 2 1] =
      [(40, 7), (12, 7), (7, 2), (2, 1), (1, 0)] := by decide

theorem paper_example : gcd 47 40 = 1 ∧ iterations 47 40 = 5 := by
  rw [gcd_correct, iterations_eq_runFuel]
  decide

/-- Numerical data transcribed from Table 1 (p. 475). -/
def table1 : List (ℕ × ℕ) :=
  [(1, 1), (3, 1), (4, 3), (10, 7), (15, 11), (37, 26), (56, 41),
   (137, 100), (209, 153), (511, 373), (780, 571), (1906, 1395),
   (2911, 2131), (7113, 5206), (10864, 7953), (26545, 19432),
   (40545, 29681), (99067, 72521), (151316, 110771), (369722, 270655)]

/-- The constructed candidates reproduce every entry of the paper's Table 1. -/
theorem table1_candidates : (List.range 20).map (fun n => candidate (n + 1)) = table1 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Table 1's pairs require respectively 1 through 20 iterations.
This finite check makes no claim of minimality. -/
theorem table1_iterations : table1.map (fun p => iterations p.1 p.2) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  simp only [table1, List.map_cons, List.map_nil, iterations_eq_runFuel]
  decide

end Lsbgcd
