import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaFullLevelCoverR0175
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaRelativeKatoR0169
run_cmd Lean.activateScoped `ArithmeticThetaThetaEvaluationR0212
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `SheafOfModules
run_cmd Lean.activateScoped `W
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaUniversalEvaluationR0213.arbitrary_even_theta_rigidification)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (ArithmeticThetaThetaEvaluationR0212.thetaIdeal R W G M).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaThetaEvaluationR0212.thetaMap R W G M) = ArithmeticThetaThetaEvaluationR0212.thetaIdeal R W G M ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaUniversalEvaluationR0213.arbitrary_even_theta_rigidification
