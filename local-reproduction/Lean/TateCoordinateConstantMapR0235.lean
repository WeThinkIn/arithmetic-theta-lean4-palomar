import BoundaryConstantsDefinitionsR0235
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaBoundaryConstantsR0235
namespace TateCoordinateConstantMapR0235
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaTateSeries ArithmeticThetaCubicModelR0144
open ArithmeticThetaCompactifiedDifferentialR0145 (root curve)

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]

lemma map_inverse (ι : k →+* l) (p : PowerSeries k) :
    PowerSeries.map ι p⁻¹ = (PowerSeries.map ι p)⁻¹ := by
  by_cases h : PowerSeries.constantCoeff p = 0
  · rw [PowerSeries.inv_eq_zero.mpr h, map_zero, PowerSeries.inv_eq_zero.mpr]
    change ι (PowerSeries.constantCoeff p) = 0
    rw [h, map_zero]
  · have hh : PowerSeries.constantCoeff (PowerSeries.map ι p) ≠ 0 := by
      change ι (PowerSeries.constantCoeff p) ≠ 0
      exact (map_ne_zero_iff ι ι.injective).mpr h
    apply (PowerSeries.eq_inv_iff_mul_eq_one hh).mpr
    rw [← map_mul, PowerSeries.inv_mul_cancel _ h, map_one]

lemma map_tateX (ι : k →+* l) (d i : ℕ) (a : k) :
    PowerSeries.map ι (tateX d i a) = tateX d i (ι a) := by
  have hp (N : ℕ) : PowerSeries.map ι (partialX d i a N) = partialX d i (ι a) N := by
    simp [partialX, xTerm, monomial, map_inverse, map_inv₀, map_ofNat]
  ext n
  simpa only [PowerSeries.coeff_map, tateX, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff n) (hp (n+1))

lemma map_root (ι : k →+* l) (L : ℕ) (j : Fin 3) :
    laurentMap ι (root k L j) = root l L j := by
  have h := (Classical.choose_spec
    (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι).1).1
  change laurentMap ι (algebraMap (PowerSeries k) (LaurentSeries k) _) = _
  change ArithmeticThetaCoefficientNormDescentR0157.IsLaurentMap k l ι (laurentMap ι) at h
  rw [h]
  congr 1
  simp only [ArithmeticThetaCoefficientNormDescentR0157.baseMap, rootSeries]
  split_ifs <;> simp [map_tateX]

lemma map_curve (ι : k →+* l) (L : ℕ) :
    (TateCurve k L).map (laurentMap ι) = TateCurve l L := by
  ext <;> simp [TateCurve, curve, map_root]

open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

lemma exists_coordinate_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) (V : WeierstrassCurve S)
    (hV : W.map f = V) :
    ∃ b : Curve S V ⟶ Curve R W,
      IsPullback b (structureMap S V) (structureMap R W) (Spec.map (CommRingCat.ofHom f)) ∧
      origin S V ≫ b = Spec.map (CommRingCat.ofHom f) ≫ origin R W ∧
      ∃ χ : ChartRing R W →+* ChartRing S V,
        χ.comp (chartScalar R W) = (chartScalar S V).comp f ∧
        χ (xOverZ W.toProjective) = xOverZ V.toProjective ∧
        χ (yOverZ W.toProjective) = yOverZ V.toProjective ∧
        chartInclusion S V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W := by
  subst V
  obtain ⟨φ, hφ, hc⟩ := exists_isCoefficientHom W.toProjective f
  have hb := isPullback_projMap_of_isCoefficientHom W.toProjective f φ hφ hc
  obtain ⟨χ, hχ, hx, hy⟩ :=
    exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota W.toProjective f φ hφ hc
  refine ⟨Proj.map φ hφ, hb, ?_, χ, ?_, hx, hy, hχ⟩
  · obtain ⟨ho, hox, hoz⟩ := isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
    obtain ⟨ho', hox', hoz'⟩ := isOriginChartSection_kwZeroSect_kwYChartEval (W.map f).toProjective
    exact comp_projMap_eq_of_isOriginChartSection W.toProjective f φ hφ hc
      (kwZeroSect R W) (kwZeroSect S (W.map f)) _ ho hox hoz _ ho' hox' hoz'
  · have he : Spec.map (CommRingCat.ofHom (χ.comp (chartScalar R W))) =
        Spec.map (CommRingCat.ofHom ((chartScalar S (W.map f)).comp f)) := by
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, chartScalar, CommRingCat.ofHom_hom,
        Spec.map_preimage]
      dsimp only [chartInclusion, structureMap]
      rw [← Category.assoc, ← hχ, Category.assoc, hb.w, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

lemma tate_chart_ext (L : ℕ) {B : Type} [CommRing B]
    (χ ψ : ChartRing (LaurentSeries k) (TateCurve k L) →+* B)
    (hs : χ.comp (chartScalar (LaurentSeries k) (TateCurve k L)) =
      ψ.comp (chartScalar (LaurentSeries k) (TateCurve k L)))
    (hx : χ (xOverZ (TateCurve k L).toProjective) = ψ (xOverZ (TateCurve k L).toProjective))
    (hy : χ (yOverZ (TateCurve k L).toProjective) = ψ (yOverZ (TateCurve k L).toProjective)) :
    χ = ψ := by
  have hsc : chartScalar (LaurentSeries k) (TateCurve k L) =
      ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart.chartScalar k L := by
    unfold chartScalar
    rw [show chartInclusion (LaurentSeries k) (TateCurve k L) ≫
        structureMap (LaurentSeries k) (TateCurve k L) = _ from
      ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart.chart_structure k L]
    rw [Spec.preimage_map]
    rfl
  obtain ⟨e, he, hex, hey⟩ :=
    ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart.exists_chartEquiv k L
  have hse (a : LaurentSeries k) : e.symm (algebraMap (LaurentSeries k) (CubicRing k L) a) =
      chartScalar (LaurentSeries k) (TateCurve k L) a := by
    apply e.injective
    rw [e.apply_symm_apply, hsc, he]
  have hxe : e.symm (cubicCoordinate k L false) = xOverZ (TateCurve k L).toProjective := by
    apply e.injective
    rw [e.apply_symm_apply, hex]
  have hye : e.symm (cubicCoordinate k L true) = yOverZ (TateCurve k L).toProjective := by
    apply e.injective
    rw [e.apply_symm_apply, hey]
  have hh : χ.comp e.symm.toRingHom = ψ.comp e.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change χ (e.symm (algebraMap (LaurentSeries k) (CubicRing k L) a)) =
        ψ (e.symm (algebraMap (LaurentSeries k) (CubicRing k L) a))
      rw [hse]
      exact RingHom.congr_fun hs a
    · intro i
      fin_cases i
      · change χ (e.symm (cubicCoordinate k L false)) = ψ (e.symm (cubicCoordinate k L false))
        rw [hxe, hx]
      · change χ (e.symm (cubicCoordinate k L true)) = ψ (e.symm (cubicCoordinate k L true))
        rw [hye, hy]
  ext a
  simpa using RingHom.congr_fun hh (e a)

lemma curveMap_unique (ι : k →+* l) (L : ℕ)
    (b c : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (hc : CurveMap ι L c) : b = c := by
  obtain ⟨χ, hχs, hχx, hχy, hχ⟩ := hb.2.2
  obtain ⟨ψ, hψs, hψx, hψy, hψ⟩ := hc.2.2
  have he : χ = ψ := tate_chart_ext L χ ψ (hχs.trans hψs.symm)
    (hχx.trans hψx.symm) (hχy.trans hψy.symm)
  haveI := isProper_projModelStrCR (TateCurve k L).toProjective
  apply hom_ext_of_zChartIota_comp_eq (LaurentSeries l) (TateCurve l L) b c
  exact hχ.trans ((congrArg (fun a => Spec.map (CommRingCat.ofHom a) ≫
    chartInclusion (LaurentSeries k) (TateCurve k L)) he).trans hψ.symm)

end TateCoordinateConstantMapR0235

theorem tate_coordinate_constant_map :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ),
      3 ≤ L → Even L → ∃! b : Quiver.Hom
        (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries l) (ArithmeticThetaTateCuspsR0181.TateCurve l L))
        (ArithmeticThetaRelativeKatoR0169.Curve (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L)),
        ArithmeticThetaBoundaryConstantsR0235.CurveMap ι L b := by
  intro k l _ _ _ _ ι L _ _
  obtain ⟨b, hb⟩ := TateCoordinateConstantMapR0235.exists_coordinate_map (laurentMap ι)
    (ArithmeticThetaTateCuspsR0181.TateCurve k L) (ArithmeticThetaTateCuspsR0181.TateCurve l L)
    (TateCoordinateConstantMapR0235.map_curve ι L)
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact TateCoordinateConstantMapR0235.curveMap_unique ι L c b hc hb

end ArithmeticThetaBoundaryConstantsR0235

#print axioms ArithmeticThetaBoundaryConstantsR0235.tate_coordinate_constant_map
