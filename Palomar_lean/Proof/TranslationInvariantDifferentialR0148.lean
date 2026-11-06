module

public import WeightedAffineExtensionR0148
public import AffineTranslationChainRuleR0148

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCubicModelR0144
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
open ArithmeticThetaDifferentialRecoveryR0148
open ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule

/-- The normalized differential is invariant under every base-rational translation,
on all opens and all regular functions. -/
theorem translation_invariant_differential :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (p : ArithmeticThetaHodgeFourTorsionR0147.Point k M), ArithmeticThetaHodgeFourTorsionR0147.DifferentialWeight k M δ (ArithmeticThetaHodgeFourTorsionR0147.translation k M G p) 1 := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY G hG e heN P
  let C := genericScheme k M
  let W := complement k M s
  letI : IsIntegral C := generic_integral k h3 M hM
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  letI : IsIso (translation k M G P) := translation_isIso k M G P
  refine ⟨translation_over k M G P, ?_⟩
  apply weighted_affine_extension (LaurentSeries k) C (genericStructure k M) e
    (translation k M G P) 1 W (complement_isAffineOpen k h3 M hM s hs X hX)
  intro a
  simpa only [InverseDifferentialSign.coefficient, frameDerivative,
    ArithmeticThetaCompactifiedDifferentialR0145.differentialAt, map_one, one_mul] using
    affine_translation_chain_rule k r hr h3 T he M hM s hs X Y hX hY G hG e heN P a

#print axioms translation_invariant_differential
end ArithmeticThetaHodgeFourTorsionR0147
