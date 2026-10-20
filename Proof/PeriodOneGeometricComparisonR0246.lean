module

public import PeriodOneCoefficientDescentR0246

@[expose] public section

/-! The actual period-one cubic and its pointed Cartesian coefficient comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ArithmeticThetaPeriodOneR0246
namespace GeometricComparison
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177

variable (k : Type) [Field k] [CharZero k]

lemma curve_map (ell : LaurentSeries k →+* LaurentSeries k)
    (he : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell) :
    (periodOneCurve k).map ell = ArithmeticThetaTateCuspsR0181.TateCurve k 4 := by
  have hc (j : Fin 3) :
      ell (algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k j)) =
        algebraMap (PowerSeries k) (LaurentSeries k) (ramifiedCoefficient k j) := by
    rw [he]
    exact congrArg (algebraMap (PowerSeries k) (LaurentSeries k))
      (period_one_coefficient_descent k j)
  ext1 <;> simp only [periodOneCurve, WeierstrassCurve.map, hc, map_zero] <;> simp [
    ArithmeticThetaTateCuspsR0181.TateCurve,
    ArithmeticThetaCompactifiedDifferentialR0145.curve,
    ArithmeticThetaCompactifiedDifferentialR0145.root, ramifiedCoefficient]

lemma elliptic : (periodOneCurve k).IsElliptic := by
  obtain ⟨ell, ⟨he, _⟩, _⟩ :=
    ArithmeticThetaRamifiedPeriodR0155.ramified_laurent_extension k 4 (by decide)
  have ht : (ArithmeticThetaTateCuspsR0181.TateCurve k 4).IsElliptic :=
    ArithmeticThetaTateCuspsR0181.TateFullLevelMarking.elliptic k 4 (by decide)
      (by decide)
  have hm : ((periodOneCurve k).map ell).IsElliptic := (curve_map k ell he).symm ▸ ht
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  intro hz
  have hn := ((periodOneCurve k).map ell).isUnit_Δ.ne_zero
  apply hn
  rw [WeierstrassCurve.map_Δ, hz, map_zero]

private lemma transport_comparison {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (f : R →+* S)
    (h : W.map f = V) :
    ∃ (b : Curve S V ⟶ Curve R W) (a : ChartRing R W →+* ChartRing S V),
      IsPullback b (structureMap S V) (structureMap R W)
        (Spec.map (CommRingCat.ofHom f)) ∧
      origin S V ≫ b = Spec.map (CommRingCat.ofHom f) ≫ origin R W ∧
      Spec.map (CommRingCat.ofHom a) ≫ chartInclusion R W = chartInclusion S V ≫ b ∧
      a (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
        WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective ∧
      a (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
        WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective := by
  subst V
  obtain ⟨b, a, hb, hbo, ha, hx, hy, _⟩ :=
    NormalFormConstruction.coefficient_comparison W f
  exact ⟨b, a, hb, hbo, ha, hx, hy⟩

lemma comparison (ell : LaurentSeries k →+* LaurentSeries k)
    (h : (periodOneCurve k).map ell = ArithmeticThetaTateCuspsR0181.TateCurve k 4) :
    Nonempty (CoordinateComparison k ell) := by
  obtain ⟨b, a, hb, hbo, ha, hx, hy⟩ :=
    transport_comparison (periodOneCurve k)
      (ArithmeticThetaTateCuspsR0181.TateCurve k 4) ell h
  exact ⟨{
    map := b
    cartesian := hb
    pointed := hbo
    chartMap := a
    chart_eq := ha
    x_eq := hx
    y_eq := hy }⟩

end GeometricComparison

/-- Ellipticity descends from the ramified Tate cubic. Every actual Laurent
extension gives the pointed Cartesian comparison preserving both coordinates. -/
theorem period_one_geometric_comparison :
    ∀ (k : Type) [Field k] [CharZero k],
      (periodOneCurve k).IsElliptic ∧
      ∀ ell : LaurentSeries k →+* LaurentSeries k,
        ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell →
        (periodOneCurve k).map ell = ArithmeticThetaTateCuspsR0181.TateCurve k 4 ∧
          Nonempty (CoordinateComparison k ell) := by
  intro k _ _
  refine ⟨GeometricComparison.elliptic k, ?_⟩
  intro ell he
  have h := GeometricComparison.curve_map k ell he
  exact ⟨h, GeometricComparison.comparison k ell h⟩

#print axioms period_one_geometric_comparison
end ArithmeticThetaPeriodOneR0246
