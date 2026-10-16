module

import all Lsbgcd.Algorithm
import all Lsbgcd.Balancing
import all Lsbgcd.BinaryImplementation
import all Lsbgcd.BitCost
import all Lsbgcd.Candidates
import all Lsbgcd.ClosedForms
import all Lsbgcd.Complexity
import all Lsbgcd.Computation
import all Lsbgcd.ContinuantOrder
import all Lsbgcd.Continuants
import all Lsbgcd.EuclideanComparison
import all Lsbgcd.Examples
import all Lsbgcd.Frontier
import all Lsbgcd.MainRecurrence
import all Lsbgcd.Minimality
import all Lsbgcd.PaperCorollaries
import all Lsbgcd.PartialReduction
import all Lsbgcd.ProofObligations
import all Lsbgcd.Ramharter
import all Lsbgcd.RamharterBoundary
import all Lsbgcd.RamharterExtrema
import all Lsbgcd.RamharterFinite
import all Lsbgcd.RamharterMatrix
import all Lsbgcd.RamharterMode
import all Lsbgcd.RamharterOrientation
import all Lsbgcd.RamharterShape
import all Lsbgcd.RamharterSort
import all Lsbgcd.RamharterSortingCore
import all Lsbgcd.RamharterWeighted
import all Lsbgcd.RamharterWeightedExtrema
import all Lsbgcd.Recurrences
import all Lsbgcd.Reduction
import all Lsbgcd.SharpComplexity
import all Lsbgcd.Specification
import all Lsbgcd.SqrtThreeContinuedFraction
import all Lsbgcd.Steps
import all Lsbgcd.SumSquares
import all Lsbgcd.Validity
import all Lsbgcd.Words
meta import Lean

/- Audit every declaration originating in a project module, including private
   declarations and definitions. Only Lean's standard logical axioms are allowed;
   in particular, unfinished proofs and additional axioms fail this check.
   Private declarations are visible only through `import all`, so every project
   module is imported that way; the check below fails if one is missing. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for moduleName in env.header.moduleNames do
    unless (`Lsbgcd).isPrefixOf moduleName do continue
    unless env.header.imports.any (fun i => i.module == moduleName && i.importAll) do
      throwError "Add `import all {moduleName}` to scripts/Audit.lean"
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    unless (`Lsbgcd).isPrefixOf moduleName do continue
    for name in data.constNames do
      let axioms ← collectAxioms name
      let forbidden := axioms.filter fun dependency => !allowed.contains dependency
      unless forbidden.isEmpty do
        throwError "{name} depends on forbidden axioms: {forbidden}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} project declarations; allowed: {allowed}"
