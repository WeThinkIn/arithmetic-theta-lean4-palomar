import NormalizationSmoothCurve

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField
open ArithmeticThetaNormalizationFinite ArithmeticThetaSmoothPrerequisites

namespace ArithmeticThetaGeometricDegree

universe u

noncomputable section

/-!
The actual normalization map is flat.  The preceding chart-dimension bridge
identifies every nonempty normalization chart with the integral closure of a
one-dimensional smooth chart.  `normalization_smooth_relative_curve` then
constructs the smooth structure on the actual normalization over the given
characteristic-zero field.  Mathlib's standard smooth-to-flat instance gives
the required scheme morphism flatness.
-/
theorem normalization_finite_flat :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f],
      ∀ (E : Type u) [Field E] [Algebra X.functionField E]
        [FiniteDimensional X.functionField E],
        AlgebraicGeometry.Flat (ArithmeticThetaNormalization.extensionFromNormalization X E) := by
  intro X hX k hk hcz f hs hlf hrd E hE hAlg hFin
  let h := ArithmeticThetaNormalization.extensionFromNormalization X E
  let Y := ArithmeticThetaNormalization.extensionNormalization X E
  apply (HasRingHomProperty.iff_exists_appLE (P := @AlgebraicGeometry.Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left).mpr
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := h y) (U := ⊤) (by trivial)
  let : Nonempty U := ⟨⟨_, hyU⟩⟩
  let V := h ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage h
  have hyV : y ∈ V := hyU
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  let := functionField_charZero X k f
  let := smooth_locallyNoetherian X k f
  let : IsNoetherianRing Γ(X, U) := smooth_affine_noetherian X k f U hU
  let : IsIntegrallyClosed Γ(X, U) :=
    ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed X k f U hU
  let : Ring.DimensionLEOne Γ(X, U) := smooth_relative_curve_dimension X k f U hU
  let : IsDedekindDomain Γ(X, U) := { }
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsDedekindDomain (integralClosure Γ(X, U) E) :=
    integralClosure.isDedekindDomain Γ(X, U) X.functionField E
  letI := baseSectionsAlgebra X E U
  letI := baseSectionsTower X E U
  letI : Module.IsTorsionFree Γ(X, U) E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    apply IsFractionRing.injective Γ(X, U) X.functionField
    apply (algebraMap X.functionField E).injective
    simpa only [IsScalarTower.algebraMap_apply Γ(X, U) X.functionField E] using hab
  letI := ((h.app U).hom.toAlgebra)
  let e : Γ(Y, V) ≃ₐ[Γ(X, U)] integralClosure Γ(X, U) E :=
    normalizationChartAlgEquiv X E U hU
  have hflatClosure : (algebraMap Γ(X, U) (integralClosure Γ(X, U) E)).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflatChart : (h.app U).hom.Flat := by
    apply (RingHom.Flat.comp_iff_of_bijective_left
      (f := (h.app U).hom) (g := e.toRingEquiv.toRingHom) e.toRingEquiv.bijective).mp
    have heq : (e.toRingEquiv.toRingHom.comp (h.app U).hom :
        Γ(X, U) →+* integralClosure Γ(X, U) E) =
        algebraMap Γ(X, U) (integralClosure Γ(X, U) E) := by
      apply RingHom.ext
      intro a
      apply Subtype.ext
      have hecomm := e.commutes a
      change e ((h.app U).hom a) =
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) E)) a at hecomm
      exact congrArg (fun z : integralClosure Γ(X, U) E => (z : E)) hecomm
    rw [heq]
    exact hflatClosure
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, ?_, ?_⟩
  · exact le_rfl
  · have happ : (h.appLE U V (le_rfl : V ≤ h ⁻¹ᵁ U)).hom = (h.app U).hom := by
      rw [Scheme.Hom.appLE_eq_app]
    rw [happ]
    exact hflatChart

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.normalization_finite_flat
