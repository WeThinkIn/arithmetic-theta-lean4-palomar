module

public import SelectedRootFieldR0228
public import AcceptedRootProvidersR0228
public import AmbientBranchValuesR0227
public import AlgebraicBranchFiniteModelR0226

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaAmbientCompletedRootsR0227
open ArithmeticThetaConstantExtensionR0225 (Omega)

/-- Realize the prescribed roots over their exact finite generated subfield,
then transport the same branch and its full section values to the ambient field. -/
theorem ambient_prescribed_roots :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space), CategoryTheory.CategoryStruct.comp f X.map = ArithmeticThetaTateCuspsR0181.diskStructure (ArithmeticThetaConstantExtensionR0225.Omega k) → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion (ArithmeticThetaConstantExtensionR0225.Omega k)) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ∃ M : ArithmeticThetaAmbientCompletedRootsR0227.AlgebraicModel k X J n s F f h E r K0, ArithmeticThetaAmbientCompletedRootsR0227.AmbientValues M := by
  intro k _ _ X J hJ n s hn F hF f hf hdom h hh E _ _ r hr K0 hK0
  obtain ⟨hfinite, _, r0, hr0, heq⟩ :=
    selected_root_field (Omega k) E X.space f J n s hn F h hh r hr
  letI : FiniteDimensional (LaurentSeries (Omega k)) (selectedField (Omega k) E s r) :=
    hfinite
  letI : Algebra.IsAlgebraic (LaurentSeries (Omega k))
      (selectedField (Omega k) E s r) := inferInstance
  obtain ⟨B, hcentre, T, hX, hT, hmodel⟩ :=
    ArithmeticThetaAlgebraicBranchesR0226.algebraic_branch_finite_model
      k X J hJ n s hn F hF f hf hdom h hh
      (selectedField (Omega k) E s r) r0 heq K0 hK0
  let M : AlgebraicModel k X J n s F f h E r K0 :=
    { field := selectedField (Omega k) E s r
      field_eq := rfl
      finite := hfinite
      prescribed := r0
      prescribed_eq := hr0
      branch := B
      centre := hcentre
      realization := T
      base_projective := hX
      cover_projective := hT
      finite_model := hmodel }
  exact ⟨M, ambient_branch_values k X J n s F f h E r K0 M⟩

#print axioms ambient_prescribed_roots
end ArithmeticThetaAmbientCompletedRootsR0227
