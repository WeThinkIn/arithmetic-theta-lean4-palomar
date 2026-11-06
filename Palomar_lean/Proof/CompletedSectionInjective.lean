module

public import NormalOrderCriterion
public import CompletionUniformizer
public import SectionCompletionDefinitions
public import GenericLineCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

universe u v w
noncomputable section
namespace ArithmeticThetaSectionCompletion

/-- The completed expansion in one actual codimension-one frame detects global
sections of the actual line bundle. -/
theorem completed_section_injective
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (H : X.Modules)
    (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (i : ι) (x : X)
    (hx : x ∈ C.opens i) (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (hc : Order.coheight x = 1) :
    Function.Injective
      (fun s : Γ(H, ⊤) => completedSection X H C s i x hx κ e) := by
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normal_stalk_dvr X hN x hc
  have hexp :
      Function.Injective (completionExpansion (X.presheaf.stalk x) κ e) :=
    completion_expansion_injective _ _ e
  intro s t hst
  have hgerm : sectionGerm X H C s i x hx = sectionGerm X H C t i x hx := by
    apply hexp
    simpa [completedSection] using hst
  apply sectionCoefficient_injective X H hH (C.opens i) (C.frame i)
  change X.germToFunctionField (C.opens i)
      (sectionCoordinate X H (C.opens i) (C.frame i) s) =
    X.germToFunctionField (C.opens i)
      (sectionCoordinate X H (C.opens i) (C.frame i) t)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hgerm

#print axioms ArithmeticThetaSectionCompletion.completed_section_injective

end ArithmeticThetaSectionCompletion
