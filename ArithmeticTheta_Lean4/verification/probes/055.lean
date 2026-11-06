import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaEvenMarkingTorsorR0216
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaMultiplierKeyR0217
run_cmd Lean.activateScoped `ArithmeticThetaPhaseFreeKeyR0219
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `SheafOfModules
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaPhaseFreeKeyR0219.phase_free_key)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∃! κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaPhaseFreeKeyR0219.phase_free_key
