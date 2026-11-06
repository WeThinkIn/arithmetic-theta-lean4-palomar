import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeDiscriminantR0244
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b) (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F), ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d → ArithmeticThetaSchemeDiscriminantR0244.IsD2 k τ F e → ArithmeticThetaSchemeDiscriminantR0244.pull C d = e))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality
