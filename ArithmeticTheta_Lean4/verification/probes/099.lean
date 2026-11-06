import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaEvenMarkingTorsorR0216
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaPhaseFreeKeyR0219
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `F
run_cmd Lean.activateScoped `P
run_cmd Lean.activateScoped `P.point
run_cmd Lean.activateScoped `Q
run_cmd Lean.activateScoped `Q.point
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `T
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaPhaseFreeKeyR0219.phase_free_multiplier_base_change)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∃! v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K, ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaPhaseFreeKeyR0219.phase_free_multiplier_base_change
