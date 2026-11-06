module

public import CanonicalKatoFieldAgreementR0252
public import PeriodOneFullKatoNormR0248

@[expose] public section

/-! The specified canonical unit has the full period-one expansion for every
actual coordinate evaluation and every supplied origin law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaSchemeKatoExpansionR0252
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaPeriodOneNormR0248
open ArithmeticThetaGeneralEllipticKatoR0168

/-- Equality of the actual laws follows from their common identity section. -/
private lemma origin_law_eq (F : Type) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (G H : ArithmeticThetaGeneralEllipticKatoR0168.Law F W)
    (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G)
    (hH : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W H) : G = H := by
  have hone : (G.one (𝟙 _)).val = (H.one (𝟙 _)).val :=
    (hG.1 _).trans (hH.1 _).symm
  apply ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext G H
  · intro V t x y
    exact WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
      W.toProjective G H hone t x y
  · intro V t
    exact Subtype.ext ((hG.1 t).trans (hH.1 t).symm)

/-- Transfer the accepted complete product to the germ of this same unit. -/
theorem canonical_period_one_expansion :
∀ (k : Type) [Field k] [CharZero k] [(ArithmeticThetaPeriodOneNormR0248.periodCurve k).IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.periodCurve k))] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve k (ArithmeticThetaPeriodOneNormR0248.periodCurve k))] (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.periodCurve k)), ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G → ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G c, ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit (LaurentSeries k) (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G c v → ArithmeticThetaSchemeKatoExpansionR0252.PeriodUnitExpansion k G c v := by
  intro k _ _ _ _ _ G hG c hc hc6 v hv
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have hv' : ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit
      (LaurentSeries k) (periodCurve k) G c v := by
    exact (congrArg (fun a : Algebra ℚ (LaurentSeries k) =>
      @ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit
        (LaurentSeries k) _ (periodCurve k) G a c v)
      (Subsingleton.elim _ _)).mp hv
  obtain ⟨hU, hvfield⟩ := canonical_kato_field_agreement
    (LaurentSeries k) (periodCurve k) G hG c hc hc6 v hv'
  refine ⟨hU, ?_⟩
  intro ev hev
  obtain ⟨hI, hN, H, hH, ev0, hev0, _⟩ := period_one_full_kato_norm k
  have hGH : G = H := origin_law_eq (LaurentSeries k) (periodCurve k) G H hG hH
  obtain ⟨g, ⟨hg, hexp⟩, _⟩ := hev0.2.2 c hc hc6
  have hgG : IsKatoFunction (LaurentSeries k) (periodCurve k) G c g := by
    rw [hGH]
    exact hg
  obtain ⟨f, hf, huniq⟩ := general_kato_existence
    (LaurentSeries k) (periodCurve k) G hG c hc hc6
  have heq := (huniq _ hvfield).trans (huniq g hgG).symm
  have heveq : ev = ev0 :=
    FunctionFieldEvaluationProof.unique k (periodCurve k) 1 ev ev0 hev hev0.1
  rw [heveq, heq]
  exact hexp

end ArithmeticThetaSchemeKatoExpansionR0252

#print axioms ArithmeticThetaSchemeKatoExpansionR0252.canonical_period_one_expansion
