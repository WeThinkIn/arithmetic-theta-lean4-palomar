import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `A.toQuadraticForm'
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → ∀ (B : ℚ) (x : Fin n → ℤ), x ∈ ArithmeticThetaLDLEnumerationR0229.enumerate n A B ↔ ArithmeticThetaLDLEnumerationR0229.energy A (fun i => (x i : ℚ)) ≤ B))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration
