import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoNormR0251
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoUnitR0250
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 2) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 3) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization
