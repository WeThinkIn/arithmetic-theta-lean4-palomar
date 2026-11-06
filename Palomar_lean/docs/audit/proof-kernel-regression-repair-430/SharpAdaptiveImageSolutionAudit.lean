module
import all SharpAdaptiveImageSolution
import Lean
open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `SharpAdaptiveImageSolution | throwError "Module not imported"
  let mut checked : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unexpected axioms for {name}: {axioms}"
    checked := checked + 1
  unless checked > 0 do throwError "No declarations checked"
  logInfo m!"SharpAdaptiveImageSolution_ALL_DECLARATIONS_STANDARD_AXIOMS {checked}"
