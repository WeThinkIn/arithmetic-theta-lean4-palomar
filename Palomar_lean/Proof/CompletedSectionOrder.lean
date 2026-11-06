module

public import NormalOrderCriterion
public import CompletionUniformizer
public import SchemeExpansionOrder
public import SectionCompletionDefinitions
public import SectionOrderDefinitions
public import GenericLineCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

universe u v w
noncomputable section
namespace ArithmeticThetaSectionCompletion

/-- The order of a nonzero actual line-section agrees with the order of its
completed local expansion in any chosen power-series coordinate. -/
theorem completed_section_order
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : NormalAffine X) (H : X.Modules)
    (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i : ι)
    (x : X) (hx : x ∈ C.opens i) (κ : Type w) [Field κ]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries κ)
    (hc : Order.coheight x = 1) (hs : s ≠ 0) :
    ArithmeticThetaSectionOrder.localOrder X H C s i x =
      ((completedSection X H C s i x hx κ e).order.toNat : ℤ) := by
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    normal_stalk_dvr X hN x hc
  let π : X.presheaf.stalk x :=
    Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  have hπ : Irreducible π :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  have horder :
      (completionExpansion (X.presheaf.stalk x) κ e π).order = 1 :=
    completion_uniformizer_order _ _ e π hπ
  have hcoef :
      sectionCoefficient X H (C.opens i) (C.frame i) s ≠ 0 := by
    intro hzero
    apply hs
    apply sectionCoefficient_injective X H hH (C.opens i) (C.frame i)
    rw [hzero]
    simp [sectionCoefficient, sectionCoordinate]
  have hgerm : sectionGerm X H C s i x hx ≠ 0 := by
    intro hz
    apply hcoef
    change X.germToFunctionField (C.opens i)
      (sectionCoordinate X H (C.opens i) (C.frame i) s) = 0
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
    change algebraMap (X.presheaf.stalk x) X.functionField (sectionGerm X H C s i x hx) = 0
    rw [hz, map_zero]
  have h := ArithmeticThetaFormalOrder.scheme_expansion_order
    X x hc κ (completionExpansion (X.presheaf.stalk x) κ e) π hπ horder
    (sectionGerm X H C s i x hx) hgerm
  simpa [ArithmeticThetaSectionOrder.localOrder, completedSection,
    completionExpansion, sectionGerm, sectionCoefficient] using h

#print axioms ArithmeticThetaSectionCompletion.completed_section_order

end ArithmeticThetaSectionCompletion
