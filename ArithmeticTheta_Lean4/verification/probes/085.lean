import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeDiscriminantR0244
run_cmd Lean.activateScoped `ArithmeticThetaSchemeKatoUnitR0250
run_cmd Lean.activateScoped `C
run_cmd Lean.activateScoped `C.map
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `H.curve
run_cmd Lean.activateScoped `H.curve.presheaf
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `TopologicalSpace
run_cmd Lean.activateScoped `TopologicalSpace.Opens
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (H : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E H b, ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c) (w : ArithmeticThetaSchemeKatoUnitR0250.UnitSection H c), ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v → ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit H k τ c w → ∃ e : ArithmeticThetaSchemeKatoUnitR0250.complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (ArithmeticThetaSchemeKatoUnitR0250.complement E c), (w : H.curve.presheaf.obj (Opposite.op (ArithmeticThetaSchemeKatoUnitR0250.complement H c))) = C.map.appLE _ _ e (v : _)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality
