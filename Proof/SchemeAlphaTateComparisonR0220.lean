module

public import AlphaLevelReductionR0220
public import FourTorsionTateBehaviorR0190

@[expose] public section

/-! The intrinsic scheme alpha has the complete Tate expansion in the prescribed frame. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaKeyTateR0220
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaSchemeHodgeR0205

/-- Apply the all-affine-test condition to the inclusion-compatible ideal map,
then preserve the signed section under level reduction before using the full
Tate expansion in the specified normalized differential frame. -/
theorem scheme_alpha_tate_comparison : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ), 0 < N → 4 ∣ N → ∀ (T : ArithmeticThetaTateCuspsR0181.TateLevel k N), ∀ (S : AlgebraicGeometry.Scheme) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4) (A : ArithmeticThetaKeyTateR0220.TateTest k N T E M) (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k N), ArithmeticThetaBoundaryHodgeR0182.Normalized k N δ → ∀ a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = N/4) ∧ ArithmeticThetaKeyTateR0220.alphaAt k N T E M A a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k N δ)) ∧ (∀ ζ : k, IsPrimitiveRoot ζ N → ArithmeticThetaTateCuspsR0181.CanonicalMarking k N ζ T → ArithmeticThetaKeyTateR0220.alphaAt k N T E M A a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k N ^ 2)) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k N δ)) := by
  intro k _ _ N hN h4 T S E M A δ hδ a ha
  letI := T.elliptic
  have hfour : ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha
      (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k N)
      T.law 4 A.marking (alphaAt k N T E M A a) := by
    exact (ha (A.affine k N T)).2
      (SchemeAlphaSection.idealIso E M (A.affine k N T))
      (SchemeAlphaSection.idealIso_compatible E M (A.affine k N T))
  have hfull := (alpha_level_reduction (LaurentSeries k)
    (ArithmeticThetaTateCuspsR0181.TateCurve k N) T.law T.originLaw
    N hN h4 T.marking A.marking A.reduces (alphaAt k N T E M A a)).mpr hfour
  exact ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior
    k N hN h4 T δ hδ (alphaAt k N T E M A a) hfull

end ArithmeticThetaKeyTateR0220

#print axioms ArithmeticThetaKeyTateR0220.scheme_alpha_tate_comparison
