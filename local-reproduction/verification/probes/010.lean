import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalAlgorithm
run_cmd Lean.activateScoped `Int

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaOrthogonalAlgorithm.computed_natural_data)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → (∀ i, 0 < (ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i ∧ Even ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i) ∧ ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i : ℤ) = (ArithmeticThetaOrthogonalAlgorithm.norms A) i) ∧ ArithmeticThetaOrthogonalAlgorithm.indexValue A = ∏ i : Fin n, ((ArithmeticThetaOrthogonalAlgorithm.basisMatrix A) i i).toNat ∧ 0 < ArithmeticThetaOrthogonalAlgorithm.indexValue A))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaOrthogonalAlgorithm.computed_natural_data
