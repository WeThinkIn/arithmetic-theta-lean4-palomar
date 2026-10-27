import AcceptedRootProvidersR0228
import AmbientPrescribedRootsR0228

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaAmbientCompletedRootsR0227

/-- The completed disk at any closed point supports the simultaneous root
construction for every generating frame and every prescribed ambient field. -/
theorem smooth_point_simultaneous_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ x : X.space, IsClosed ({x} : Set X.space) → ∃ f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space, ArithmeticThetaAmbientCompletedRootsR0227.IsCompletedDisk (ArithmeticThetaConstantExtensionR0225.Omega k) X x f ∧ (∃ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h) ∧ ∀ h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by
  intro k _ _ X J hJ n s hn F hF x hx
  obtain ⟨f, hf, hframe⟩ :=
    completed_point_disk (ArithmeticThetaConstantExtensionR0225.Omega k) X x hx J hJ
  refine ⟨f, hf, hframe, ?_⟩
  intro h hh E _ _ r hr K0 hK0
  exact ambient_prescribed_roots k X J hJ n s hn F hF f hf.1 hf.2.2.1
    h hh E r hr K0 hK0

#print axioms smooth_point_simultaneous_roots
end ArithmeticThetaAmbientCompletedRootsR0227
