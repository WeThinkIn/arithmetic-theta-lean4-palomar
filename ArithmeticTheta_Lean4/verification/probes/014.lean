import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBinary
run_cmd Lean.activateScoped `Int

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaBinary.ambient_realization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ j : Fin 3, (ArithmeticThetaBinary.embeddings j).det ≠ 0 ∧ (ArithmeticThetaBinary.embeddings j).transpose * (ArithmeticThetaBinary.forms 0).map (Int.castRingHom ℚ) * ArithmeticThetaBinary.embeddings j = (![1,3,1] : Fin 3 → ℚ) j • (ArithmeticThetaBinary.forms j).map (Int.castRingHom ℚ)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaBinary.ambient_realization
