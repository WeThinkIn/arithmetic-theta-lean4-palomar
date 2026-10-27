import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBinary
run_cmd Lean.activateScoped `U

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaBinary.all_positive_classes)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ a b c : ℤ, 0 < a → 4*a*c-b^2 = 80 → ArithmeticThetaBinary.gramContent a b c = 2 → ∃ (j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ), IsUnit U.det ∧ U.transpose * ArithmeticThetaBinary.gram a b c * U = ArithmeticThetaBinary.forms j))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaBinary.all_positive_classes
