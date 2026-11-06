module
import all MainAndComponentsSolution
import Lean
open Lean Elab Command Meta
run_cmd liftTermElabM do
  let n := ``ArithmeticThetaPalomarMain172.explicitFiniteDetermination
  let current ← getConstInfo n
  let (data, _) ← readModuleData "/home/Palomar/workspace/arithmetic-theta/evidence/main-solution-265/Solution.olean"
  let mut found := false
  for name in data.constNames, ci in data.constants do
    if name == n then
      unless current.type == ci.type do throwError "Original main proposition AST differs"
      unless current.levelParams == ci.levelParams do throwError "Original main universes differ"
      found := true
  unless found do throwError "Original main declaration absent"
  logInfo "EXACT_265_MAIN_TYPE_AST_AND_UNIVERSES_MATCH true"
#print axioms ArithmeticThetaPalomarMain172.explicitFiniteDetermination
