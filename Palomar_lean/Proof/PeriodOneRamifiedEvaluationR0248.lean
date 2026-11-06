module

public import PeriodOneFunctionFieldEvaluationR0248
public import RamifiedCubicKatoEvaluationR0248
public import PeriodOneChartEvaluationR0248

@[expose] public section

/-! The literal evaluation square for the specified pointed parameter change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaPeriodOneNormR0248
namespace RamifiedEvaluationProof
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaGeneralEllipticKatoR0168

variable (k : Type) [Field k] [CharZero k]

lemma origin_base_change
    [(periodCurve k).IsElliptic] [(ramifiedCurve k 4).IsElliptic]
    (ell : LaurentSeries k →+* LaurentSeries k)
    (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell)
    (G : Law (LaurentSeries k) (periodCurve k))
    (H : Law (LaurentSeries k) (ramifiedCurve k 4))
    (hG : IsOriginLaw (LaurentSeries k) (periodCurve k) G)
    (hH : IsOriginLaw (LaurentSeries k) (ramifiedCurve k 4) H) :
    IsBaseChange (LaurentSeries k) (LaurentSeries k)
      (periodCurve k) (ramifiedCurve k 4) G H ell C.map := by
  refine ⟨C.cartesian, C.pointed, ?_⟩
  obtain ⟨J, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ell (structureMap (LaurentSeries k) (periodCurve k))
      (structureMap (LaurentSeries k) (ramifiedCurve k 4)) C.map C.cartesian G
  have hone : (H.one (𝟙 _)).val = (J.one (𝟙 _)).val := by
    apply C.cartesian.hom_ext
    · have hp : origin (LaurentSeries k) (ramifiedCurve k 4) ≫ C.map =
          Spec.map (CommRingCat.ofHom ell) ≫ origin (LaurentSeries k) (periodCurve k) :=
        C.pointed
      rw [hH.1, Category.id_comp, hp, ho, Category.id_comp, hG.1]
    · exact (H.one (𝟙 _)).property.trans (J.one (𝟙 _)).property.symm
  have hlaw : H = J :=
    ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.law_ext H J
      (fun t x y => RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
        (ramifiedCurve k 4).toProjective H J hone t x y)
      (by
        intro T t
        apply Subtype.ext
        have h1 := congrArg Subtype.val (H.one_natural (𝟙 _) t t (Category.comp_id t))
        have h2 := congrArg Subtype.val (J.one_natural (𝟙 _) t t (Category.comp_id t))
        exact h1.symm.trans ((congrArg (fun z => t ≫ z) hone).trans h2))
  intro n
  rw [hlaw]
  exact BaseChange.nsmul_comp ell _ C.map C.cartesian G J hm ho n

lemma chart_scalars (ell : LaurentSeries k →+* LaurentSeries k)
    (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell) (b : LaurentSeries k) :
    C.chartMap (ArithmeticThetaLegendreComparisonR0177.chartScalar _ (periodCurve k) b) =
      ArithmeticThetaLegendreComparisonR0177.chartScalar _ (ramifiedCurve k 4) (ell b) := by
  have h : CommRingCat.ofHom
      (C.chartMap.comp (ArithmeticThetaLegendreComparisonR0177.chartScalar _ (periodCurve k))) =
      CommRingCat.ofHom
        ((ArithmeticThetaLegendreComparisonR0177.chartScalar _ (ramifiedCurve k 4)).comp ell) := by
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp,
      ArithmeticThetaLegendreComparisonR0177.chartScalar,
      CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [← Category.assoc, C.chart_eq, Category.assoc, C.cartesian.w, ← Category.assoc]
  exact congrArg (fun f => f.hom b) h

lemma scalar_square (ell : LaurentSeries k →+* LaurentSeries k)
    (he : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell)
    (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi) :
    (baseMap k).comp ell = psi.comp (baseMap k) := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro b
  change ∀ b, ell (HahnSeries.ofPowerSeries ℤ k b) =
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.expand 4 (by decide) b) at he
  change ∀ b, psi (HahnSeries.ofPowerSeries ℤ (Coeff k) b) =
    HahnSeries.ofPowerSeries ℤ (Coeff k) (PowerSeries.expand 4 (by decide) b) at hp
  change baseMap k (ell (HahnSeries.ofPowerSeries ℤ k b)) =
    psi (baseMap k (HahnSeries.ofPowerSeries ℤ k b))
  rw [he, ChartEvaluationProof.baseMap_powerSeries, ChartEvaluationProof.baseMap_powerSeries, hp]
  exact congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k))
    (PowerSeries.map_expand _ _ _ _)

lemma coordinate_square (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi) :
    psi (xSeries k 1) = xSeries k 4 ∧ psi (ySeries k 1) = ySeries k 4 := by
  letI : CharZero (Coeff k) := charZero_of_injective_ringHom
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k).injective
  change ∀ b, psi (HahnSeries.ofPowerSeries ℤ (Coeff k) b) =
    HahnSeries.ofPowerSeries ℤ (Coeff k) (PowerSeries.expand 4 (by decide) b) at hp
  have ha : ArithmeticThetaTateSeries.Admissible 1 0
      (ArithmeticThetaLaurentNormR0064.w k) := by
    exact ⟨by decide, by decide, ChartEvaluationProof.w_ne_zero k,
      fun _ => ChartEvaluationProof.w_ne_one k⟩
  have h := ArithmeticThetaTateBridges.ramified_substitution 4 1 0
    (ArithmeticThetaLaurentNormR0064.w k) (by decide) ha
  constructor
  · change psi (HahnSeries.ofPowerSeries ℤ (Coeff k) _) = _
    rw [hp]
    exact congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k)) h.1.symm
  · change psi (HahnSeries.ofPowerSeries ℤ (Coeff k) _) = _
    rw [hp]
    exact congrArg (HahnSeries.ofPowerSeries ℤ (Coeff k)) h.2.symm

lemma chart_square (ell : LaurentSeries k →+* LaurentSeries k)
    (he : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell)
    (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell)
    (a : ChartRing k (periodCurve k) →+* Series k)
    (a4 : ChartRing k (ramifiedCurve k 4) →+* Series k)
    (ha : IsChartEvaluation k (periodCurve k) 1 a)
    (ha4 : IsChartEvaluation k (ramifiedCurve k 4) 4 a4)
    (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi) :
    a4.comp C.chartMap = psi.comp a := by
  apply P2MW.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration.WMLocal.zChart_ringHom_ext
    (periodCurve k)
  · apply RingHom.ext
    intro b
    have hs := ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction.chartScalar_apply
      (periodCurve k) b
    exact (congrArg (a4.comp C.chartMap) hs.symm).trans
      ((congrArg a4 (chart_scalars k ell C b)).trans ((ha4.1 (ell b)).trans
        ((RingHom.congr_fun (scalar_square k ell he psi hp) b).trans
          ((congrArg psi (ha.1 b).symm).trans (congrArg (psi.comp a) hs)))))
  · exact (congrArg a4 C.x_eq).trans (ha4.2.1.trans
      (((coordinate_square k psi hp).1.symm).trans (congrArg psi ha.2.1.symm)))
  · exact (congrArg a4 C.y_eq).trans (ha4.2.2.trans
      (((coordinate_square k psi hp).2.symm).trans (congrArg psi ha.2.2.symm)))

/-- Cancellation of compatible affine and generic-point squares, independent of
the presentations of the two schemes. -/
lemma generic_evaluation_square {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    {A B F : Type} [CommRing A] [CommRing B] [Field F]
    (i : Spec (CommRingCat.of A) ⟶ X) (j : Spec (CommRingCat.of B) ⟶ Y)
    (f : Y ⟶ X) (b : A →+* B)
    (hb : Spec.map (CommRingCat.ofHom b) ≫ i = j ≫ f)
    (a : A →+* F) (a4 : B →+* F)
    (ev : X.functionField →+* F) (ev4 : Y.functionField →+* F)
    (hs : Spec.map (CommRingCat.ofHom a) ≫ i =
      Spec.map (CommRingCat.ofHom ev) ≫ X.fromSpecStalk (genericPoint X))
    (hs4 : Spec.map (CommRingCat.ofHom a4) ≫ j =
      Spec.map (CommRingCat.ofHom ev4) ≫ Y.fromSpecStalk (genericPoint Y))
    (psi : F →+* F) (hc : a4.comp b = psi.comp a)
    (alpha : X.functionField →+* Y.functionField)
    (halpha : ArithmeticThetaGeometricNormR0150.IsFieldMap f alpha) :
    ev4.comp alpha = psi.comp ev := by
  suffices h : CommRingCat.ofHom (ev4.comp alpha) = CommRingCat.ofHom (psi.comp ev) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [← halpha, ← Category.assoc, ← hs4, Category.assoc, ← hb,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hs]

lemma evaluation_square
    [IsIntegral (Curve k (periodCurve k))] [IsIntegral (Curve k (ramifiedCurve k 4))]
    (ell : LaurentSeries k →+* LaurentSeries k)
    (he : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell)
    (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell)
    (ev : (Curve k (periodCurve k)).functionField →+* Series k)
    (ev4 : (Curve k (ramifiedCurve k 4)).functionField →+* Series k)
    (hv : IsEvaluation k (periodCurve k) 1 ev)
    (hv4 : IsEvaluation k (ramifiedCurve k 4) 4 ev4)
    (psi : Series k →+* Series k)
    (hp : ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi)
    (alpha : (Curve k (periodCurve k)).functionField →+*
      (Curve k (ramifiedCurve k 4)).functionField)
    (halpha : ArithmeticThetaGeometricNormR0150.IsFieldMap C.map alpha) :
    ev4.comp alpha = psi.comp ev := by
  obtain ⟨a, ha, hs⟩ := hv
  obtain ⟨a4, ha4, hs4⟩ := hv4
  have hc := chart_square k ell he C a a4 ha ha4 psi hp
  exact generic_evaluation_square (chartInclusion k (periodCurve k))
    (chartInclusion k (ramifiedCurve k 4)) C.map C.chartMap C.chart_eq
    a a4 ev ev4 hs hs4 psi hc alpha halpha

end RamifiedEvaluationProof

open CategoryTheory AlgebraicGeometry

/-- The same geometric field map commutes with full evaluation and transports
the divisor and every coprime multiplication norm of each normalized Kato function. -/
theorem period_one_ramified_evaluation :
    ∀ (k : Type) [Field k] [CharZero k]
      [(periodCurve k).IsElliptic] [(ramifiedCurve k 4).IsElliptic]
      [IsIntegral (Curve k (periodCurve k))]
      [IsLocallyNoetherian (Curve k (periodCurve k))]
      [IsIntegral (Curve k (ramifiedCurve k 4))]
      [IsLocallyNoetherian (Curve k (ramifiedCurve k 4))]
      (ell : LaurentSeries k →+* LaurentSeries k),
      ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension k 4 (by decide) ell →
      ∀ (C : ArithmeticThetaPeriodOneR0246.CoordinateComparison k ell)
        (G : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) (periodCurve k))
        (G4 : ArithmeticThetaGeneralEllipticKatoR0168.Law (LaurentSeries k) (ramifiedCurve k 4)),
      ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) (periodCurve k) G →
      ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (LaurentSeries k) (ramifiedCurve k 4) G4 →
      ∀ (ev : (Curve k (periodCurve k)).functionField →+* Series k)
        (ev4 : (Curve k (ramifiedCurve k 4)).functionField →+* Series k),
      IsEvaluation k (periodCurve k) 1 ev → IsEvaluation k (ramifiedCurve k 4) 4 ev4 →
      ∀ psi : Series k →+* Series k,
      ArithmeticThetaRamifiedPeriodR0154.IsLaurentExtension (Coeff k) 4 (by decide) psi →
      ∃! a : (Curve k (periodCurve k)).functionField →+*
          (Curve k (ramifiedCurve k 4)).functionField,
        ArithmeticThetaGeometricNormR0150.IsFieldMap C.map a ∧
        ev4.comp a = psi.comp ev ∧
        ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
        ∀ g : (Curve k (periodCurve k)).functionField,
        ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
          (LaurentSeries k) (periodCurve k) G c g →
        ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
          (LaurentSeries k) (ramifiedCurve k 4) G4 c (a g) := by
  intro k _ _ _ _ _ _ _ _ ell he C G G4 hG hG4 ev ev4 hv hv4 psi hp
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have hb := RamifiedEvaluationProof.origin_base_change k ell C G G4 hG hG4
  obtain ⟨a, ⟨ha, hk⟩, hu⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_base_change
    (LaurentSeries k) (periodCurve k) G hG
    (LaurentSeries k) (ramifiedCurve k 4) G4 hG4 ell C.map hb
  exact ⟨a, ⟨ha, RamifiedEvaluationProof.evaluation_square k ell he C ev ev4 hv hv4
    psi hp a ha, hk⟩, fun b hb => hu b ⟨hb.1, hb.2.2⟩⟩

#print axioms period_one_ramified_evaluation
end ArithmeticThetaPeriodOneNormR0248
