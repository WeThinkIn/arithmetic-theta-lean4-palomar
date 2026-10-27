import BoundaryConstantsDefinitionsR0235

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaBoundaryConstantsR0235
namespace TateMarkingConstantTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreComparisonR0177

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]

omit [CharZero k] [CharZero l] in
lemma map_inverse (ι : k →+* l) (f : PowerSeries k) :
    PowerSeries.map ι f⁻¹ = (PowerSeries.map ι f)⁻¹ := by
  by_cases h : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr h, map_zero,
      PowerSeries.inv_eq_zero.mpr (show PowerSeries.constantCoeff (PowerSeries.map ι f) = 0 from by
        change ι (PowerSeries.constantCoeff f) = 0; rw [h, map_zero])]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by
      change ι (PowerSeries.constantCoeff f) ≠ 0
      exact (map_ne_zero ι).mpr h)).mpr
    rw [← map_mul, PowerSeries.inv_mul_cancel _ h, map_one]

open ArithmeticThetaTateSeries
lemma map_partialX (ι : k →+* l) (d i N : ℕ) (a : k) :
    PowerSeries.map ι (partialX d i a N) = partialX d i (ι a) N := by
  simp [partialX, xTerm, monomial, map_inverse, map_inv₀, map_ofNat]
lemma map_partialY (ι : k →+* l) (d i N : ℕ) (a : k) :
    PowerSeries.map ι (partialY d i a N) = partialY d i (ι a) N := by
  simp [partialY, yTerm, monomial, map_inverse, map_inv₀, map_ofNat]
lemma map_tateX (ι : k →+* l) (d i : ℕ) (a : k) :
    PowerSeries.map ι (tateX d i a) = tateX d i (ι a) := by
  ext n
  simpa only [PowerSeries.coeff_map, tateX, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff n) (map_partialX ι d i (n+1) a)
lemma map_tateY (ι : k →+* l) (d i : ℕ) (a : k) :
    PowerSeries.map ι (tateY d i a) = tateY d i (ι a) := by
  ext n
  simpa only [PowerSeries.coeff_map, tateY, PowerSeries.coeff_mk] using
    congrArg (PowerSeries.coeff n) (map_partialY ι d i (n+1) a)

lemma laurent_powerSeries (ι : k →+* l) (f : PowerSeries k) :
    laurentMap ι (algebraMap (PowerSeries k) (LaurentSeries k) f) =
      algebraMap (PowerSeries l) (LaurentSeries l) (PowerSeries.map ι f) :=
  (Classical.choose_spec
    (ArithmeticThetaCoefficientNormDescentR0157.coefficient_completed_maps k l ι).1).1 f

lemma law_exists (ι : k →+* l) (L : ℕ)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b) (A : TateLevel k L) :
    ∃ H : Law (LaurentSeries l) (TateCurve l L),
      IsOriginLaw (LaurentSeries l) (TateCurve l L) H ∧
      IsBaseChange (LaurentSeries k) (TateCurve k L) A.law
        (LaurentSeries l) (TateCurve l L) H (laurentMap ι) b := by
  obtain ⟨H, hm, ho⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      (laurentMap ι) _ _ b hb.1 A.law
  have hH : IsOriginLaw (LaurentSeries l) (TateCurve l L) H := by
    constructor
    · intro V t
      apply hb.1.hom_ext
      · rw [ho, A.originLaw.1]
        simp only [Category.assoc, hb.2.1]
        rfl
      · rw [(H.one t).property, Category.assoc, BaseChange.origin_over, Category.comp_id]
    · intro V t x y
      apply Subtype.ext
      apply hb.1.hom_ext
      · rw [hm, hm, A.originLaw.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  exact ⟨H, hH, hb.1, hb.2.1,
    ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
      (laurentMap ι) _ b hb.1 A.law H hm ho⟩

lemma coordinates_transfer (ι : k →+* l) (L : ℕ)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (hb : CurveMap ι L b)
    (P : Puncture k ⟶ Curve (LaurentSeries k) (TateCurve k L))
    (Q : Puncture l ⟶ Curve (LaurentSeries l) (TateCurve l L))
    (hQ : Q ≫ structureMap (LaurentSeries l) (TateCurve l L) = 𝟙 _)
    (ha : Disjoint (Set.range Q) (Set.range (origin (LaurentSeries l) (TateCurve l L))))
    (hc : Q ≫ b = punctureMap ι ≫ P)
    (x y : LaurentSeries k) (hP : HasCoordinates _ _ P x y) :
    HasCoordinates _ _ Q (laurentMap ι x) (laurentMap ι y) := by
  obtain ⟨χ, hχs, hχx, hχy, hχ⟩ := hb.2.2
  obtain ⟨ρ, hρ⟩ := TwoTorsionAffineCoordinates.exists_chart_factorization _ Q ha
  obtain ⟨_, σ, hσ, hσx, hσy⟩ := hP
  have he : ρ.comp χ = (laurentMap ι).comp σ := by
    change (CommRingCat.ofHom (ρ.comp χ)).hom = (CommRingCat.ofHom ((laurentMap ι).comp σ)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    let : Mono (chartInclusion (LaurentSeries k) (TateCurve k L)) :=
      inferInstanceAs (Mono (WeierstrassCurve.DrinfeldGlobal.zChartι (TateCurve k L).toProjective))
    apply (cancel_mono (chartInclusion (LaurentSeries k) (TateCurve k L))).mp
    simp only [Category.assoc, ← hχ, ← hσ]
    rw [← Category.assoc, ← hρ]
    exact hc
  refine ⟨hQ, ρ, hρ, ?_, ?_⟩
  · have h := RingHom.congr_fun he (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)
    simpa only [RingHom.comp_apply, hχx, hσx] using h
  · have h := RingHom.congr_fun he (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)
    simpa only [RingHom.comp_apply, hχy, hσy] using h

end TateMarkingConstantTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaFullLevelCoverR0175
open TateMarkingConstantTransfer

/-- Cartesian transport preserves every ordered label and its literal Tate coordinates. -/
theorem tate_marking_constant_transfer :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ),
      3 ≤ L → Even L →
      ∀ (b : Quiver.Hom (Curve (LaurentSeries l) (TateCurve l L))
        (Curve (LaurentSeries k) (TateCurve k L))), CurveMap ι L b →
      ∀ (A : TateLevel k L), ∃ B : TateLevel l L, Transfers ι A B b ∧
        (∀ ζ : k, CanonicalMarking k L ζ A → CanonicalMarking l L (ι ζ) B) := by
  intro k l _ _ _ _ ι L hL heven b hb A
  obtain ⟨H, hH, hbase⟩ := law_exists ι L b hb A
  let : (TateCurve l L).IsElliptic := TateFullLevelMarking.elliptic l L hL heven
  let A' : FullLevel (LaurentSeries k) (TateCurve k L) A.law L
      ((𝟙 (Puncture l)) ≫ punctureMap ι) :=
    BaseChange.restrict A.marking (punctureMap ι) (by simp)
  let M := BaseChange.up hbase A.originLaw hH A'
  let B : TateLevel l L := ⟨inferInstance, H, hH, M⟩
  have hc (i j : Fin L) :
      coordinatePoint (LaurentSeries l) (TateCurve l L) B.law B.marking i j ≫ b =
        punctureMap ι ≫ coordinatePoint (LaurentSeries k) (TateCurve k L) A.law A.marking i j := by
    have hp := congrArg Subtype.val (BaseChange.point_combination hbase A.originLaw hH
      (𝟙 (Puncture l)) M.x M.y i.val j.val)
    have hx : BaseChange.point hbase (𝟙 (Puncture l)) M.x = A'.x :=
      BaseChange.point_symm hbase _ _
    have hy : BaseChange.point hbase (𝟙 (Puncture l)) M.y = A'.y :=
      BaseChange.point_symm hbase _ _
    rw [hx, hy] at hp
    exact hp.trans (Representability.combination_natural _ _ A.law _ _
      (punctureMap ι) (by simp only [Category.comp_id, Category.id_comp]; rfl) A.marking.x A.marking.y i.val j.val).symm
  refine ⟨B, ⟨hbase, hc⟩, ?_⟩
  intro ζ hζ i j hij
  have hd := coordinates_transfer ι L b hb _ _
    (H.mul (𝟙 _) (H.nsmul (𝟙 _) i.val M.x) (H.nsmul (𝟙 _) j.val M.y)).property
    (M.avoids i j hij) (hc i j) _ _ (hζ i j hij)
  simpa only [laurent_powerSeries, map_tateX, map_tateY, map_pow, B, coordinatePoint] using hd

end ArithmeticThetaBoundaryConstantsR0235
#print axioms ArithmeticThetaBoundaryConstantsR0235.tate_marking_constant_transfer
