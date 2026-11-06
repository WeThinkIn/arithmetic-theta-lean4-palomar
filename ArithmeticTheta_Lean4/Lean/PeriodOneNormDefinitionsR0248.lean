import RationalTateDiscriminantDefinitionsR0247
import UnsplitKatoFullExpansionR0158
import GeneralKatoBaseChangeR0168

/-! The full generic-coordinate expansion of the actual period-one Tate curve.
All maps are constrained by the structural scalar map and both coordinates.
The existence, faithfulness and Kato expansion are separate obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaPeriodOneNormR0248
open CategoryTheory AlgebraicGeometry

variable (k : Type) [Field k] [CharZero k]
abbrev Coeff := ArithmeticThetaLaurentNormR0064.Coeff k
abbrev Series := ArithmeticThetaLaurentNormR0064.Series k
abbrev Curve (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaGeneralEllipticKatoR0168.Curve (LaurentSeries k) W
abbrev ChartRing (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) W
abbrev chartInclusion (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) W
abbrev periodCurve := ArithmeticThetaPeriodOneR0246.periodOneCurve k
abbrev ramifiedCurve (r : ℕ) := ArithmeticThetaTateCuspsR0181.TateCurve k r

/-- Coefficient extension fixes the formal parameter and embeds k into k(w). -/
def baseMap : LaurentSeries k →+* Series k :=
  ArithmeticThetaRationalTateR0247.seriesMap
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k)

/-- Full literal Tate sums at the transcendental multiplicative coordinate w. -/
def xSeries (r : ℕ) : Series k :=
  HahnSeries.ofPowerSeries ℤ (Coeff k)
    (ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k))
def ySeries (r : ℕ) : Series k :=
  HahnSeries.ofPowerSeries ℤ (Coeff k)
    (ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k))

def IsChartEvaluation (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    (a : ChartRing k W →+* Series k) : Prop :=
  (∀ b : LaurentSeries k,
    a (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W b) =
      baseMap k b) ∧
  a (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = xSeries k r ∧
  a (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = ySeries k r

/-- The generic-point square ties evaluation to the same projective curve.
It contains no Kato function and assumes no product identity. -/
def IsEvaluation (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ)
    [IsIntegral (Curve k W)]
    (ev : (Curve k W).functionField →+* Series k) : Prop :=
  ∃ a : ChartRing k W →+* Series k, IsChartEvaluation k W r a ∧
    Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W =
      Spec.map (CommRingCat.ofHom ev) ≫ (Curve k W).fromSpecStalk (genericPoint (Curve k W))

/-- Source norm at Q itself: construct the geometry and ONE faithful expansion
map, then every c>1 prime to six has its uniquely normalized full product. -/
def PeriodOneNorm : Prop :=
  ∃ hI : IsIntegral (Curve k (periodCurve k)),
  ∃ hN : IsLocallyNoetherian (Curve k (periodCurve k)),
  letI := hI
  letI := hN
  ∃ G : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) (periodCurve k),
    ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) (periodCurve k) G ∧
    ∃! ev : (Curve k (periodCurve k)).functionField →+* Series k,
      IsEvaluation k (periodCurve k) 1 ev ∧ Function.Injective ev ∧
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
        ∃! g : (Curve k (periodCurve k)).functionField,
          ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
            (LaurentSeries k) (periodCurve k) G c g ∧
          ArithmeticThetaUnsplitExpansionR0158.HasExpansion k 1 c 0 (ev g)

end ArithmeticThetaPeriodOneNormR0248
