import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaRank16

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaRank16.two_column_kernel)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ v : Fin 2 → ℂ, (∑ i, v i • ArithmeticThetaRank16.columns i) = 0 ↔ ∃ t : ℂ, v = ![t, -t]))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaRank16.two_column_kernel
