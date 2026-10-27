import AlgebraicBranchValuationR0226
import AlgebraicBranchEquationR0226

/-! Realization of the original algebraic field roots by the accepted finite model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAlgebraicBranchesR0226
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaConstantExtensionR0225
open ArithmeticThetaValuativeRootsR0223

/-- Construct the valuation and centre, transport the prescribed equations with
exactly the original frame, and apply the finite constant-extension theorem. -/
theorem algebraic_branch_finite_model :
∀ (k : Type) [Field k] [CharZero k] (X : ArithmeticThetaFiniteFieldModelsR0221.Curve (ArithmeticThetaConstantExtensionR0225.Omega k)) (J : X.space.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (n s : ℕ), 0 < n → ∀ (F : Fin s → ArithmeticThetaFiniteFieldModelsR0221.Sections (ArithmeticThetaTensorPower.tensorPower X.space J n)), (∀ j, F j ≠ 0) → ∀ (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk (ArithmeticThetaConstantExtensionR0225.Omega k)) X.space), CategoryTheory.CategoryStruct.comp f X.map = ArithmeticThetaTateCuspsR0181.diskStructure (ArithmeticThetaConstantExtensionR0225.Omega k) → AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaTateCuspsR0181.genericInclusion (ArithmeticThetaConstantExtensionR0225.Omega k)) f) → ∀ (h : ArithmeticThetaFiniteFieldModelsR0221.Sections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (E : Type) [Field E] [Algebra (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] [Algebra.IsAlgebraic (LaurentSeries (ArithmeticThetaConstantExtensionR0225.Omega k)) E] (r : Fin s → E), (∀ j, ArithmeticThetaAlgebraicBranchesR0226.Equation f J n (F j) h (r j)) → ∀ K0 : ArithmeticThetaConstantExtensionR0225.FieldStage k, FiniteDimensional k K0 → ArithmeticThetaAlgebraicBranchesR0226.Realization k X J n s F f h E r K0 := by
  intro k _ _ X J hJ n s hn F hF f hf hdom h hh E _ _ _ r hr K0 hK0
  obtain ⟨B, hcentre, htriangle⟩ := algebraic_branch_valuation (Omega k) E
  have hcompat := fun t => RingHom.congr_fun B.compatible t
  have hd := ValuedExtensionPrescribedRootsR0223.extended_disk_dominant
    (Omega k) E B.ring B.inclusion hcompat f hdom
  have hh' := ValuedExtensionPrescribedRootsR0223.extended_frame_isFrame
    (Omega k) E B.ring B.inclusion f J h hh
  have heq (j : Fin s) :=
    (algebraic_branch_equation (Omega k) E B.toValuationExtension X.space
      f J n (F j) h (r j)).mp (hr j)
  have hbase : (B.centre ≫ extendedDisk (Omega k) E B.ring B.inclusion f) ≫
      X.map = 𝟙 _ := by
    unfold extendedDisk
    rw [← Category.assoc B.centre, Category.assoc, hf, htriangle]
    unfold ArithmeticThetaTateCuspsR0181.diskStructure
    rw [← Spec.map_comp]
    have hc : (PowerSeries.constantCoeff : PowerSeries (Omega k) →+* Omega k).comp
        (algebraMap (Omega k) (PowerSeries (Omega k))) = RingHom.id (Omega k) := by
      ext x
      simp
    change Spec.map (CommRingCat.ofHom
      ((PowerSeries.constantCoeff : PowerSeries (Omega k) →+* Omega k).comp
        (algebraMap (Omega k) (PowerSeries (Omega k))))) = _
    rw [hc]
    exact Spec.map_id _
  obtain ⟨T, hX, hT, hmodel⟩ := prescribed_roots_finite_constant_extension
    k X J hJ n s hn F hF E B.ring
    (extendedDisk (Omega k) E B.ring B.inclusion f) hd
    (extendedFrame (Omega k) E B.ring B.inclusion f J h) hh' r heq
    B.centre hcentre hbase K0 hK0
  exact ⟨B, hcentre, T, hX, hT, hmodel⟩

#print axioms algebraic_branch_finite_model
end ArithmeticThetaAlgebraicBranchesR0226
