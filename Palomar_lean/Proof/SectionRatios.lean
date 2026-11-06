module

public import SectionCompletionDefinitions
public import SectionOrderInvariance
public import GenericLineCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

universe u v w
noncomputable section
namespace ArithmeticThetaSectionCompletion

private theorem sectionCoefficient_ne_zero_of_section_ne_zero
    (X : Scheme.{u}) [IsIntegral X]
    (H : X.Modules) (hH : IsLineBundle X H)
    {ι : Type v} (C : NormalFrameCover X H ι) (s₀ : Γ(H, ⊤)) (i : ι)
    (hs₀ : s₀ ≠ 0) :
    sectionCoefficient X H (C.opens i) (C.frame i) s₀ ≠ 0 := by
  intro hzero
  apply hs₀
  apply (sectionCoefficient_injective X H hH (C.opens i) (C.frame i))
  rw [hzero]
  simp [sectionCoefficient, sectionCoordinate]

/-- The ratio of two actual global sections is independent of the local frame. -/
theorem section_ratio_frame_independent
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s s₀ : Γ(H, ⊤)) (i j : ι) : s₀ ≠ 0 →
    sectionRatio X H C i s s₀ = sectionRatio X H C j s s₀ := by
  intro hs₀
  have hdeni := sectionCoefficient_ne_zero_of_section_ne_zero X H hH C s₀ i hs₀
  have hdenj := sectionCoefficient_ne_zero_of_section_ne_zero X H hH C s₀ j hs₀
  have hu : X.germToFunctionField (C.opens i ⊓ C.opens j)
      (overlapUnit C i j) ≠ 0 :=
    ((overlapUnit C i j).isUnit.map
      (X.germToFunctionField (C.opens i ⊓ C.opens j)).hom).ne_zero
  unfold sectionRatio
  rw [ArithmeticThetaSectionOrder.sectionCoefficient_transition X H C s i j,
    ArithmeticThetaSectionOrder.sectionCoefficient_transition X H C s₀ i j]
  field_simp [hdeni, hdenj, hu]

/-- The actual section-ratio map is injective when its reference section is nonzero. -/
theorem section_ratio_injective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s₀ : Γ(H, ⊤)) (i : ι) : s₀ ≠ 0 →
    Function.Injective (fun s : Γ(H, ⊤) => sectionRatio X H C i s s₀) := by
  intro hs₀ s t hst
  have hden := sectionCoefficient_ne_zero_of_section_ne_zero X H hH C s₀ i hs₀
  apply sectionCoefficient_injective X H hH (C.opens i) (C.frame i)
  have hst' := hst
  unfold sectionRatio at hst'
  field_simp [hden] at hst'
  exact hst'

end ArithmeticThetaSectionCompletion

#print axioms ArithmeticThetaSectionCompletion.section_ratio_frame_independent
#print axioms ArithmeticThetaSectionCompletion.section_ratio_injective
