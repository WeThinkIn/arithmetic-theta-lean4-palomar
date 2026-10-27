import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoNormR0251
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom X Y) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.Etale f], ∃! N : ArithmeticThetaSchemeKatoNormR0251.NormFamily f, ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family
