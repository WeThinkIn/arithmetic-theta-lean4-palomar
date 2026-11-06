import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaKatoInitialR0253
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeDiscriminantR0244
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoUnitR0250
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaKatoInitialR0253.scheme_five_kato_initial_characterization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E 5, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ 5 v → ∀ d : ArithmeticThetaSchemeDiscriminantR0244.Sections E, ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d ↔ ArithmeticThetaKatoInitialR0253.SchemeInitial E v d))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaKatoInitialR0253.scheme_five_kato_initial_characterization
