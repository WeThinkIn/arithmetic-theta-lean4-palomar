import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBinary
run_cmd Lean.activateScoped `Int
run_cmd Lean.activateScoped `U

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaBinary.similarity_distinct)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (i j : Fin 3), i ≠ j → ¬ ∃ (s : ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (ArithmeticThetaBinary.forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (ArithmeticThetaBinary.forms j).map (Int.castRingHom ℚ)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaBinary.similarity_distinct
