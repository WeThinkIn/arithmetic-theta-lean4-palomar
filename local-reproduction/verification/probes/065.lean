import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaElimination
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B = ArithmeticThetaComputed.coefficientMatrix A B ∧ ArithmeticThetaElimination.run (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B) = ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B) ∧ (ArithmeticThetaComputed.prefixMap B).comp (ArithmeticThetaComputed.thetaMap A) = ((ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix
