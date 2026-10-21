# Lean formalisation of the LSBGCD paper

This project targets the full mathematical development of Jeffrey Shallit and
Jonathan Sorenson, [*Analysis of a Left-Shift Binary GCD Algorithm*](https://www.sciencedirect.com/science/article/pii/S0747717184710303),
Journal of Symbolic Computation 17 (1994), 473–486.

**Theorem 1.1 is proved**, including global minimality, the order-16 recurrence,
and all six closed forms. The unconditional declaration is
[`Lsbgcd.theorem1_1`](Lsbgcd/Minimality.lean), of type `MainTheorem`.
The algorithm's correctness, the reduction theorems, the binary minimiser
classification (Theorem 5.2), and logarithmic iteration bounds are also proved.

**All numbered mathematical results are formalised**, including the general
Ramharter permutation theorem quoted as Theorem 5.1. Its declaration is
[`Lsbgcd.ramharter_theorem`](Lsbgcd/RamharterSort.lean). Theorem 1.1 and
Theorem 5.2 additionally have an independent binary-continuant proof.

**The sum-of-squares conjecture at the end of §6 is also proved**, including
uniqueness of the minimising ordered input. See
[`SumSquares.lean`](Lsbgcd/SumSquares.lean): `sum_squares_conjecture` and
`sum_squares_minimizer_unique`. The connection to the continued fraction of
`√3`, including convergence and a geometric error bound, is proved in
[`SqrtThreeContinuedFraction.lean`](Lsbgcd/SqrtThreeContinuedFraction.lean).

## Build and verification

The project uses **Lean 4.35.0 / Mathlib v4.35.0**. `lean-toolchain` selects
Lean, and `lake-manifest.json` pins Mathlib and its transitive dependencies.
Install [elan, the Lean version manager](https://github.com/leanprover/elan#installation)
if needed. On Linux or macOS:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
. "$HOME/.elan/env"
```

From the repository root, download the precompiled Mathlib cache and verify:

```sh
lake exe cache get
python3 scripts/verify.py
```

Verification uses the local Lean installation and Python 3's standard library.
The script runs:

1. `lake build` to compile the project;
2. `lake env leanchecker --verbose Lsbgcd` to replay project declarations through
   Lean's kernel, on one thread by default because each thread needs about 7 GB of
   memory (set `LEAN_NUM_THREADS` to use more);
3. `lake env lean scripts/Audit.lean` to audit the axiom dependencies of every
   declaration originating in a project module, including definitions and private
   declarations. It rejects unfinished proofs and any axioms beyond `propext`,
   `Classical.choice`, and `Quot.sound`.

Logs are retained in `build/local/build.log`, `kernel.log`, and `axioms.log`.
Any failed step makes the script exit with a nonzero status. Once Lean and the
project dependencies are installed, verification runs locally without uploading
source. For compilation alone, use `lake build`.

## Palomar statement surface

The repository is laid out for the [Palomar registry](https://palomar-registry.org/)
([submission form](https://submit.palomar-registry.org/)).
[`Challenge.lean`](Challenge.lean) is a short, Mathlib-only statement file to
audit: it defines the algorithm and states gcd correctness, Theorem 1.1,
Theorem 5.1, the §7 bound and the sum-of-squares theorem, each with `sorry`.
[`Solution.lean`](Solution.lean) proves the same declarations from the library.
[`comparator.json`](comparator.json) lists them, and
[`formalization.yaml`](formalization.yaml) records provenance, scope and
divergences from the paper.

`lake comparator` checks that every listed theorem has the same statement in
both modules, that the definitions they use are identical constants, and that
the proofs use only `propext`, `Classical.choice` and `Quot.sound`. It needs
`bwrap` (bubblewrap) on Linux:

```sh
python3 scripts/check-lean-sources.py   # module headers and file sizes
./scripts/verify-comparator.sh          # Lean, nanoda and con-ron kernels
ruby scripts/validate-formalization.rb  # metadata
```

Every source file uses the Lean module system, as Palomar requires.
`check-lean-sources.py` scans the whole working tree, so it also reports any
stray `.lean` files under the ignored `build/` directory.

## Paper correspondence

All declarations below are in namespace `Lsbgcd`.

| Paper | Lean development |
| --- | --- |
| §1 algorithm, termination, GCD correctness | [`Algorithm.lean`](Lsbgcd/Algorithm.lean): `run`, `gcd_correct`, exact iteration counter and equivalent finite evaluator. |
| §1 binary implementation and complexity | [`BinaryImplementation.lean`](Lsbgcd/BinaryImplementation.lean), [`Complexity.lean`](Lsbgcd/Complexity.lean), [`BitCost.lean`](Lsbgcd/BitCost.lean): bit-length exponent selection, product contraction, logarithmic iteration count, quadratic cost bound. |
| §2 transformations; Lemmas 3.1–3.2 | [`Steps.lean`](Lsbgcd/Steps.lean): inverse A/B transformations, branch conditions, comparison order. |
| Theorem 3.3, Corollary 3.4, Lemma 3.5 | [`Validity.lean`](Lsbgcd/Validity.lean): all four transformation cases with executable semantics and valid partial computations. |
| Lemmas 4.1–4.2, Theorem 4.3 | [`Steps.lean`](Lsbgcd/Steps.lean), [`Validity.lean`](Lsbgcd/Validity.lean), [`PartialReduction.lean`](Lsbgcd/PartialReduction.lean): monotonicity and reduction at arbitrary output endpoints. |
| Partial computations and actual executions | [`Computation.lean`](Lsbgcd/Computation.lean): every step has a valid transformation; exact iteration accounting. |
| §5 continuants; (5.2), (5.3), full matrix identity (6.1) | [`Continuants.lean`](Lsbgcd/Continuants.lean): numerator/denominator recursion, coprimality, reversal, four-entry matrix identity. |
| Admissible words and reduction of arbitrary inputs | [`Words.lean`](Lsbgcd/Words.lean), [`Reduction.lean`](Lsbgcd/Reduction.lean): every admissible word executes for its length; every input reduces to a no-larger admissible convergent with the same iteration count. |
| Theorem 5.2 and denominator tie-break | [`Frontier.lean`](Lsbgcd/Frontier.lean), [`Balancing.lean`](Lsbgcd/Balancing.lean), [`Minimality.lean`](Lsbgcd/Minimality.lean): direct domination and exchange proof, all minimisers up to reversal, unique lexicographic minimum. |
| Theorem 5.1 (general quoted result) | [`Ramharter.lean`](Lsbgcd/Ramharter.lean), [`RamharterSort.lean`](Lsbgcd/RamharterSort.lean): the displayed rank arrangement, general minimality, and uniqueness up to reversal, including repeated digits. |
| §6 candidate words and matrix recurrences | [`Candidates.lean`](Lsbgcd/Candidates.lean), [`Recurrences.lean`](Lsbgcd/Recurrences.lean): admissibility, coprimality, exact iteration counts, matrix recurrences, `Sₖ − Tₖ = 1`. |
| Theorem 1.1 recurrence and closed forms | [`MainRecurrence.lean`](Lsbgcd/MainRecurrence.lean), [`ClosedForms.lean`](Lsbgcd/ClosedForms.lean), [`Minimality.lean`](Lsbgcd/Minimality.lean): complete unconditional main theorem. |
| End of §6 sum-of-squares conjecture | [`SumSquares.lean`](Lsbgcd/SumSquares.lean): global minimality and uniqueness of consecutive terms of the printed recurrence, with exact iteration counts. |
| Continued-fraction interpretation of the §6 conjecture | [`SqrtThreeContinuedFraction.lean`](Lsbgcd/SqrtThreeContinuedFraction.lean): the truncations `[1;1,2,1,2,…]` converge to `√3`, with an explicit error bound and the proved denominator identity. |
| §7 sharp iteration bound | [`SharpComplexity.lean`](Lsbgcd/SharpComplexity.lean): coefficient `1 / log₂ √(2 + √3)`, with an explicit additive constant. |
| §7 Euclidean comparison | [`EuclideanComparison.lean`](Lsbgcd/EuclideanComparison.lean): consecutive Fibonacci worst cases, Fibonacci asymptotic, coefficient `1 / log₂ φ`, certified 26.8–27% reduction in leading coefficients. |
| Table 1 and worked example | [`Examples.lean`](Lsbgcd/Examples.lean): all 20 listed pairs and iteration counts; full `(47,40)` trace, checked by the Lean kernel. |
| Additional §1, §4, §5 and §7 claims | [`PaperCorollaries.lean`](Lsbgcd/PaperCorollaries.lean): rational continued-fraction interpretation, worst-case A₀/A₁ traces, no single infinite expansion, Table 1 minimality, certified decimal coefficients `1.053` and `1.441`. |

[`Specification.lean`](Lsbgcd/Specification.lean) defines `IsWorstCase`,
`CandidateMinimality`, `Order16`, `ClosedForms`, and `MainTheorem`, together
with the two intermediate statements `ReductionToAdmissible` (proved in
`Reduction.lean`) and `AdmissibleMinimality` (proved in `Minimality.lean`).
`Minimality.lean` combines them into the unconditional main theorem:

```lean
theorem theorem1_1 : MainTheorem
theorem candidate_minimality : CandidateMinimality
theorem isWorstCase_iff (n : ℕ) (p : ℕ × ℕ) :
  IsWorstCase n p ↔ p = candidate n
```

The complexity statement concerns the explicit bit-scan primitive model in
`BitCost.lean`. It is not a timing assertion about Lean's `Nat` evaluator or
a particular computer. The historical timing and average-iteration tables
in §7 are empirical observations. The sum-of-squares minimiser discussion
at the end of §6 is conjectural in the paper; the project now proves it.

## Sum-of-squares minimum

For every `n ≥ 2`, the unique ordered positive pair requiring exactly `n`
LSBGCD iterations and minimising `u² + v²` is `(pₙ₋₁, pₙ₋₂)`, where
`p₀ = 1`, `p₁ = 3`, `p₂ₖ = p₂ₖ₋₁ + p₂ₖ₋₂`, and
`p₂ₖ₊₁ = 2p₂ₖ + p₂ₖ₋₁` for `k ≥ 1`.
The one-iteration minimum is `(1,1)`.

The proof uses the existing reduction order, which also decreases squared
size, and the admissible-word classification in `Frontier.lean`.
For even lengths, an exact nonnegative polynomial identity shows that
`(21)ⁱ⁺ʲ` has smaller squared size than `(12)ⁱ(21)ʲ` whenever `i > 0`.
For odd lengths, the existing alternating word already dominates.
Equality through these reductions proves uniqueness.

In Lean the sequence is `sqrtThreeDenominator`. There is an apparent typo on
p. 484: the prose calls `pₙ` the numerator
of a convergent to `√3`, whereas the printed recurrence gives
`1,3,4,11,15,41,…`. These are the **denominators** of the convergents
`[1;1]`, `[1;1,2]`, `[1;1,2,1]`, etc.
The theorem follows the explicit recurrence; the finite continued-fraction
identity is proved as `convergent_sqrtThreeWord_denominator`, which states
that the denominator of `[1;1,2,1,…]` with `n + 1` partial quotients after the
initial `1` is `sqrtThreeDenominator n`.

The analytic connection is also proved: `sqrtThree_continuedFraction_tendsto`
states that these finite continued fractions converge to `√3`.
If `Cₙ` has `n` partial quotients after the initial `1`, then
`sqrtThreeConvergent_error` proves `|Cₙ − √3| ≤ (1/3)^(n/2)`, with integer
division in the exponent. The proof uses the two-step recurrence
`Cₙ₊₂ = (2Cₙ + 3)/(Cₙ + 2)`, which contracts the error by at least a factor
of three.

## General continuant proof

The general Ramharter theorem covers permutations of **arbitrary positive
integer digits**, including repeated entries. The proof retains rational
boundary values for the fixed outside digits. Strict interval-reversal
comparisons force the next two extrema to the endpoints; removing them
switches between choosing the least and greatest remaining entries.
The induction also tracks equality, proving that reversal is the only
alternative minimiser.

The supporting modules are `ContinuantOrder`, `RamharterShape`,
`RamharterBoundary`, `RamharterMatrix`, `RamharterWeighted`,
`RamharterWeightedExtrema`, `RamharterMode`, and `RamharterSortingCore`;
the header of [`RamharterSort.lean`](Lsbgcd/RamharterSort.lean) gives the role
of each.
[`RamharterExtrema.lean`](Lsbgcd/RamharterExtrema.lean) also exposes the
unweighted outermost endpoint conditions directly.

## Conventions and boundary cases

- Inputs are natural numbers; the program sorts arbitrary inputs. On ordered
  positive inputs it follows the paper's pseudocode, choosing A on a tie.
- A loop step requires a positive second input. Inequalities involving
  `2^(e−1)` are written `2*y ≤ 2^e*x`, which also handles `e = 0` exactly.
- The swapped rows of Theorem 3.3 require **`x > y`** because the algorithm
  interchanges only on strict inequality. The printed `x ≥ y` is insufficient
  for those rows; the paper's proof itself notes the strictness.
- Worst-case inputs have a positive first coordinate, including at `n = 0`.
  The zero-step minimum is therefore `(1,0)`, matching the closed forms.
- Euclid's consecutive-Fibonacci minimum for non-strict ordered inputs is
  stated for at least two divisions. The one-division minimum is `(1,1)`;
  under strict ordering it is `(2,1)`.
