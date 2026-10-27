import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `A.toQuadraticForm'
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229
run_cmd Lean.activateScoped `Fin
run_cmd Lean.activateScoped `j

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.rational_schur_completion)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix (n+1)), A.IsSymm → A.toQuadraticForm'.PosDef → 0 < A 0 0 ∧ (ArithmeticThetaLDLEnumerationR0229.schur A).IsSymm ∧ (ArithmeticThetaLDLEnumerationR0229.schur A).toQuadraticForm'.PosDef ∧ ∀ (z : ℚ) (y : Fin n → ℚ), ArithmeticThetaLDLEnumerationR0229.energy A (Fin.cons z y) = A 0 0 * (z + (∑ j : Fin n, A 0 j.succ * y j) / A 0 0)^2 + ArithmeticThetaLDLEnumerationR0229.energy (ArithmeticThetaLDLEnumerationR0229.schur A) y))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.rational_schur_completion
