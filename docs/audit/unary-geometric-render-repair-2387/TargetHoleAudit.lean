module
import all UnaryGeometricChallenge
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
run_cmd liftTermElabM do
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/unary-geometric-current-full-audit-2378/comparator.json")
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names"
  let defs := (cfg.getObjValAs? (Array String) "definition_names").toOption.getD #[]
  let env ← getEnv
  for str in names do
    let name := str.toName
    let some ci := env.find? name | throwError "Missing target {name}"
    unless ← isProp ci.type do throwError "Non-proposition target {name}"
    let some value := ci.value? (allowOpaque := true) | throwError "Missing target body {name}"
    unless value.getUsedConstants.contains `sorryAx do
      throwError "No direct target hole {name}"
  for str in defs do
    let name := str.toName
    let some ci := env.find? name | throwError "Missing definition target {name}"
    if ← isProp ci.type then throwError "Expected data definition {name}"
    let some value := ci.value? | throwError "Missing definition value {name}"
    unless value.getUsedConstants.contains `sorryAx do throwError "Missing selected definition hole {name}"
  let source ← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/unary-geometric-local-declaration-render-2373/unary-geometric/UnaryGeometricChallenge.lean"
  let literalCount := (source.splitOn "sorry").length - 1
  unless literalCount == names.size + defs.size do throwError "Literal/target count mismatch {literalCount}/{names.size}"
  logInfo m!"DIRECT_PROPOSITION_HOLES {names.size}; DEFINITION_HOLES {defs.size}; LITERAL_HOLES {literalCount}"
