import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `A.toQuadraticForm'
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229
run_cmd Lean.activateScoped `Matrix

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → (∀ i : Fin n, 0 < (ArithmeticThetaLDLEnumerationR0229.ldl n A).1 i) ∧ (∀ i : Fin n, (ArithmeticThetaLDLEnumerationR0229.ldl n A).2 i i = 1) ∧ (∀ i j : Fin n, j < i → (ArithmeticThetaLDLEnumerationR0229.ldl n A).2 i j = 0) ∧ A = (ArithmeticThetaLDLEnumerationR0229.ldl n A).2.transpose * Matrix.diagonal (ArithmeticThetaLDLEnumerationR0229.ldl n A).1 * (ArithmeticThetaLDLEnumerationR0229.ldl n A).2))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl
