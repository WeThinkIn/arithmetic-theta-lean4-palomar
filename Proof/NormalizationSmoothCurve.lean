module

public import SmoothNormalizedCurve
public import NormalizationCurveDimension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField
open ArithmeticThetaNormalizationFinite ArithmeticThetaSmoothPrerequisites

namespace ArithmeticThetaGeometricDegree

universe u

noncomputable section

/--
The actual normalization remains smooth over the characteristic-zero base.
The dimension of each actual normalization chart is obtained from
`normalization_chart_dimensionLEOne`, and its finite-type Dedekind algebra
is smooth over the characteristic-zero field.
-/
theorem normalization_smooth_relative_curve :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
      (k : Type u) [Field k] [CharZero k]
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 f],
      ∀ (E : Type u) [Field E] [Algebra X.functionField E]
        [FiniteDimensional X.functionField E],
        AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.comp
          (ArithmeticThetaNormalization.extensionFromNormalization X E) f) := by
  intro X hX k hk hcz f hs hlf hrd E hE hAlg hFin
  let := functionField_charZero X k f
  let := smooth_locallyNoetherian X k f
  let h := extensionFromNormalization X E
  let Y := extensionNormalization X E
  apply (HasRingHomProperty.iff_exists_appLE (P := @Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).left).mpr
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := h y) (U := ⊤) (by trivial)
  let : Nonempty U := ⟨⟨_, hyU⟩⟩
  let V := h ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage h
  have hyV : y ∈ V := hyU
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  let : IsNoetherianRing Γ(X,U) := smooth_affine_noetherian X k f U hU
  let : IsIntegrallyClosed Γ(X,U) :=
    ArithmeticThetaSmoothNormality.smooth_affine_integrallyClosed X k f U hU
  let : Ring.DimensionLEOne Γ(X,U) := smooth_relative_curve_dimension X k f U hU
  let : IsDedekindDomain Γ(X,U) := { }
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsDedekindDomain (integralClosure Γ(X,U) E) :=
    integralClosure.isDedekindDomain Γ(X,U) X.functionField E
  let e : Γ(Y,V) ≃+* integralClosure Γ(X,U) E :=
    normalizationChartRingEquiv X E U hU
  let : IsNoetherianRing Γ(Y,V) :=
    isNoetherianRing_of_ringEquiv (integralClosure Γ(X,U) E) e.symm
  let : Ring.DimensionLEOne Γ(Y,V) := normalization_chart_dimensionLEOne X k f E U hU
  let : IsIntegrallyClosed Γ(Y,V) := IsIntegrallyClosed.of_equiv e.symm
  let : IsDedekindDomain Γ(Y,V) := { }
  have hfinite : (h.app U).hom.Finite := normalizationChart_finite X E U hU
  have hconst : constantSectionsMap Y k (h ≫ f) V =
      (h.app U).hom.comp (constantSectionsMap X k f U) := by
    have heq := h.appLE_comp_appLE f ⊤ U V (by simp) (le_refl _)
    rw [Scheme.Hom.appLE_eq_app] at heq
    ext a
    exact congrArg (fun q => q ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) heq.symm
  let := (constantSectionsMap Y k (h ≫ f) V).toAlgebra
  have hft : (constantSectionsMap Y k (h ≫ f) V).FiniteType := by
    rw [hconst]
    have ha := (smooth_affine_structureMap X k f U hU).finitePresentation
    exact hfinite.to_finiteType.comp (RingHom.FiniteType.of_finitePresentation ha)
  let : Algebra.FiniteType k Γ(Y,V) := hft
  have hs : (constantSectionsMap Y k (h ≫ f) V).Smooth := ArithmeticThetaNormalizedCurve.dedekind_smooth k Γ(Y,V)
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨V, hV⟩, hyV, by simp, ?_⟩
  have hc := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.bijective) hs
  have heq : (constantSectionsMap Y k (h ≫ f) V).comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom =
      ((h ≫ f).appLE ⊤ V (by simp)).hom := by
    ext a
    simp [constantSectionsMap]
    rfl
  rw [heq] at hc
  exact hc

end
end ArithmeticThetaGeometricDegree

#print axioms ArithmeticThetaGeometricDegree.normalization_smooth_relative_curve
