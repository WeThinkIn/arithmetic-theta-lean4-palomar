import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaHadamard

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaHadamard.jacobi_formal)
  let expected ← Lean.Elab.Term.elabType (← `(term| ArithmeticThetaHadamard.a ^ 4 = ArithmeticThetaHadamard.b ^ 4 + ArithmeticThetaHadamard.c ^ 4))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaHadamard.jacobi_formal
