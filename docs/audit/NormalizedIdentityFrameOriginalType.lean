module

public import NormalizedIdentityFrameR0140

@[expose] public section

/-! Normalization of the actual identity pullback. All implementation helpers
are confined to this module's namespace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140
namespace NormalizedIdentityFrameR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
  (chartIso chartIso_inclusion compIso compIso_inclusion)
open ArithmeticThetaIdentitySectionsR0138
open AlgebraizedThetaSectionsR0138
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134
  (pullFrame pullFrame_isIso pullFrame_evaluation affine_pullback_inv)


lemma compIso_proof_irrel135 {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : X ⟶ Z) (h1 h2 : f ≫ g = c) (L : Z.Modules) :
    (compIso f g c h1 L).hom = (compIso f g c h2 L).hom := rfl

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
lemma pointStageFrame_transition_original_type_bridge135 (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d n N : ℕ) (h : n ≤ N) :
    pullFrame (baseReduction k n N h) (pointStageFrame k h3 M hM s hs d N) ≫
      (compIso (baseReduction k n N h) (baseRestriction k N ≫ s) (baseRestriction k n ≫ s)
        (by rw [← Category.assoc, baseInclusion_reduction]) (powerModule k M s d)).hom =
    pointStageFrame k h3 M hM s hs d n := by
  refine Eq.trans ?_ (pointStageFrame_transition k h3 M hM s hs d n N h)
  apply congrArg (fun z => pullFrame (baseReduction k n N h)
    (pointStageFrame k h3 M hM s hs d N) ≫ z)
  apply compIso_proof_irrel135


end NormalizedIdentityFrameR0140
end ArithmeticThetaGenericEvaluationR0140
end

#print axioms ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.pointStageFrame_transition_original_type_bridge135
