import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaTateSeries
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaTateSeries.basic_fourth)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ {k : Type u} [Field k] [CharZero k], ArithmeticThetaTateSeries.theta k ^ 4 = 4 * (ArithmeticThetaTateSeries.tateX 2 1 (1:k) - ArithmeticThetaTateSeries.tateX 2 0 (-1:k))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaTateSeries.basic_fourth
