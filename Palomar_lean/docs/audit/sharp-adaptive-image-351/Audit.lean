module
import all Solution
public import Lean
open Lean Elab Command in
elab "#audit351" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Nat := 0
  let some idx := env.getModuleIdx? `Solution
    | throwError "Module not imported"
  for name in env.header.moduleData[idx]!.constNames do
    let userName := (privateToUserName? name).getD name
    if userName.isInternalDetail then continue
    let axioms ← collectAxioms name
    checked := checked + 1
    logInfo m!"AXIOM351 {name}: {axioms}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      bad := bad + 1
      logError m!"UNAPPROVED351 {name}: {axioms}"
  logInfo m!"TOTAL351 checked={checked} bad={bad}"
  if checked == 0 then throwError "No module declarations inspected"
  if bad != 0 then throwError "Unexpected axiom closures"
#audit351

