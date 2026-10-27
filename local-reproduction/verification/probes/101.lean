import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaEvenMarkingTorsorR0216
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaMultiplierKeyR0217
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `SheafOfModules
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaMultiplierKeyR0217.even_point_theta_evaluation)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), (ArithmeticThetaMultiplierKeyR0217.thetaIdeal E P).IsInvertible ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaMultiplierKeyR0217.thetaLine E P) ∧ AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal (ArithmeticThetaMultiplierKeyR0217.thetaMap E P) = ArithmeticThetaMultiplierKeyR0217.thetaIdeal E P ∧ (∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e) ∧ CategoryTheory.IsIso (ArithmeticThetaMultiplierKeyR0217.generator E P) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → CategoryTheory.IsIso (ArithmeticThetaMultiplierKeyR0217.evaluation E P e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaMultiplierKeyR0217.generator E P) (ArithmeticThetaMultiplierKeyR0217.evaluation E P e) = CategoryTheory.CategoryStruct.id (SheafOfModules.unit S.ringCatSheaf) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaMultiplierKeyR0217.pushforwardLine E P)) ⊤ (ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaMultiplierKeyR0217.even_point_theta_evaluation
