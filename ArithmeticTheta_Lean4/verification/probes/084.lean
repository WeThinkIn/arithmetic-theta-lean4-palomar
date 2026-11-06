import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaRationalTateR0247
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaSchemeDiscriminantR0244
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `Quiver

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaRationalTateR0247.scheme_period_one_discriminant)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (X : AlgebraicGeometry.Scheme) (σ : Quiver.Hom X (ArithmeticThetaRelativeDiscriminantR0171.Base ℚ)) (E : ArithmeticThetaLocalWeierstrassR0203.Family X), ∃! d : ArithmeticThetaSchemeDiscriminantR0244.Sections E, ArithmeticThetaSchemeDiscriminantR0244.IsD2 ℚ σ E d ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaSchemeDiscriminantR0244.Power E) ⊤ d ∧ ArithmeticThetaRationalTateR0247.HasTateExpansions σ E d ∧ ∀ (Y : AlgebraicGeometry.Scheme) (τ : Quiver.Hom Y (ArithmeticThetaRelativeDiscriminantR0171.Base ℚ)) (F : ArithmeticThetaLocalWeierstrassR0203.Family Y) (b : Quiver.Hom Y X), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b) (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F), ArithmeticThetaSchemeDiscriminantR0244.IsD2 ℚ τ F e → ArithmeticThetaSchemeDiscriminantR0244.pull C d = e))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaRationalTateR0247.scheme_period_one_discriminant
