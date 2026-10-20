module
import all Solution
import Lean
open Lean Elab Command Meta
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
  let base := "/home/Palomar/workspace/arithmetic-theta/evidence/isogeny-alpha-cusps-package-502/Challenge"
  let parts ← readModuleDataParts #[⟨base ++ ".olean"⟩, ⟨base ++ ".olean.server"⟩, ⟨base ++ ".olean.private"⟩]
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut checked : Nat := 0
  for (data, _) in parts do
    for ci in data.constants do
      if seen.contains ci.name then continue
      if (← isProp ci.type) then continue
      seen := seen.insert ci.name
      let some original := env.find? ci.name | throwError "Missing semantic declaration {ci.name}"
      unless (← isDefEq ci.type original.type) do throwError "Semantic type differs {ci.name}"
      if let some v := ci.value? then
        let some ov := original.value? | throwError "Missing semantic body {ci.name}"
        unless (← withTransparency .all <| isDefEq v ov) do throwError "Semantic body differs {ci.name}"
      checked := checked + 1
  logInfo m!"CHALLENGE_SOLUTION_SEMANTIC_TYPES_AND_AVAILABLE_BODIES_DEF_EQ {checked}"
