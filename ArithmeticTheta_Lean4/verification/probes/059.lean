import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaAlgebraicBranchesR0226
run_cmd Lean.activateScoped `ArithmeticThetaAmbientCompletedRootsR0227
run_cmd Lean.activateScoped `ArithmeticThetaConstantExtensionR0225
run_cmd Lean.activateScoped `ArithmeticThetaFiniteFieldModelsR0221
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaTateCuspsR0181
run_cmd Lean.activateScoped `ArithmeticThetaTensorPower
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `X
run_cmd Lean.activateScoped `X.space

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAmbientCompletedRootsR0227.smooth_point_simultaneous_roots)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ x : X.space, IsClosed ({x} : Set X.space) → ∃ f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space, ArithmeticThetaAmbientCompletedRootsR0227.IsCompletedDisk (ArithmeticThetaConstantExtensionR0225.Omega k) X x f ∧ (∃ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h) ∧ ∀ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAmbientCompletedRootsR0227.smooth_point_simultaneous_roots
