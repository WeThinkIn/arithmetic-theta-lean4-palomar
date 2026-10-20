module

public import NormalizationField

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField

namespace ArithmeticThetaNormalizationFinite

universe u
noncomputable section

variable (X : Scheme.{u}) [IsIntegral X] (E : Type u) [Field E]
  [Algebra X.functionField E]

/-- Promote the actual chart ring identification using the actual outgoing pullback. -/
def normalizationChartAlgEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((extensionFromNormalization X E).app U).hom.toAlgebra
    Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) ≃ₐ[Γ(X,U)]
      integralClosure Γ(X,U) E :=
  letI := ((extensionFromNormalization X E).app U).hom.toAlgebra
  { normalizationChartRingEquiv X E U hU with
    commutes' a := Subtype.ext (normalizationChartRingEquiv_base X E U hU a) }

theorem normalizationClosure_finite [FiniteDimensional X.functionField E]
    [Algebra.IsSeparable X.functionField E] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [IsIntegrallyClosed Γ(X,U)] [IsNoetherianRing Γ(X,U)] :
    Module.Finite Γ(X,U) (integralClosure Γ(X,U) E) := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsIntegralClosure.finite Γ(X,U) X.functionField E (integralClosure Γ(X,U) E)

theorem normalizationChart_finite [FiniteDimensional X.functionField E]
    [Algebra.IsSeparable X.functionField E] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [IsIntegrallyClosed Γ(X,U)] [IsNoetherianRing Γ(X,U)] :
    ((extensionFromNormalization X E).app U).hom.Finite := by
  let := ((extensionFromNormalization X E).app U).hom.toAlgebra
  let := normalizationClosure_finite X E U hU
  exact Module.Finite.equiv (normalizationChartAlgEquiv X E U hU).symm.toLinearEquiv

variable [IsLocallyNoetherian X] [FiniteDimensional X.functionField E]
  [Algebra.IsSeparable X.functionField E]

/-- Finiteness of the actual normalization morphism, derived from base chart normality. -/
theorem extensionFromNormalization_finite
    (hX : ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X,U)) :
    IsFinite (extensionFromNormalization X E) := by
  constructor
  intro U hU
  rcases U.1.eq_empty_or_nonempty with h | h
  · have hbot : U = ⊥ := SetLike.ext' h
    subst U
    have : Subsingleton Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ ⊥) := by
      simpa using (inferInstance : Subsingleton Γ(extensionNormalization X E, ⊥))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)
  · let : Nonempty U := by simpa using h
    let := hX U hU
    let := IsLocallyNoetherian.component_noetherian (X := X) ⟨U, hU⟩
    exact normalizationChart_finite X E U hU

/-- The finite actual normalization morphism is proper. -/
theorem extensionFromNormalization_proper
    (hX : ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X,U)) :
    IsProper (extensionFromNormalization X E) := by
  let := extensionFromNormalization_finite X E hX
  infer_instance

/-- Properness over any base is preserved for this actual normalization. -/
theorem extensionNormalization_proper_over
    (hX : ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X,U))
    (S : Scheme.{u}) (f : X ⟶ S) [IsProper f] :
    IsProper (extensionFromNormalization X E ≫ f) := by
  let := extensionFromNormalization_proper X E hX
  infer_instance

/-- The actual normalization is locally Noetherian under the same genuine hypotheses. -/
theorem extensionNormalization_locallyNoetherian
    (hX : ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U], IsIntegrallyClosed Γ(X,U)) :
    IsLocallyNoetherian (extensionNormalization X E) := by
  let := extensionFromNormalization_finite X E hX
  exact LocallyOfFiniteType.isLocallyNoetherian (extensionFromNormalization X E)

end
end ArithmeticThetaNormalizationFinite
