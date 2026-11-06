import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoExpansionR0252
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoNormR0251
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoUnitR0250
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `Quiver

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSchemeKatoExpansionR0252.scheme_kato_full_tate_expansion)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (B : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom B (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family B), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃! v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ∧ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E d) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _)) ∧ ArithmeticThetaSchemeKatoExpansionR0252.TateExpansion k σ E c v))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSchemeKatoExpansionR0252.scheme_kato_full_tate_expansion
