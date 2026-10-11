import Lsbgcd

/- Audit every declaration originating in a project module, including private
   declarations and definitions. Only Lean's standard logical axioms are allowed;
   in particular, unfinished proofs and additional axioms fail this check. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
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
