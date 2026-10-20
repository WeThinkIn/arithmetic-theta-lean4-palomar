module

public import GeneralEllipticKatoDefinitionsR0168
public import ProjectivePointsEvaluationR0146
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
namespace Principality
open CategoryTheory AlgebraicGeometry NeronModelInfra
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart
variable {F : Type u} [Field F] (W : WeierstrassCurve F)

def chartScalar : F →+* ZChartRing W.toProjective :=
  (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective)
    (Submonoid.powers (coord W.toProjective 2))).comp
      (algebraMap F (projModelGradingCR W.toProjective 0))

lemma chart_structure : zChartι W.toProjective ≫ structureMap F W =
    Spec.map (CommRingCat.ofHom (chartScalar W)) := by
  rw [zChartι, structureMap, projModelStrCR,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

lemma exists_chart_equiv : ∃ e : ZChartRing W.toProjective ≃+* W.toAffine.CoordinateRing,
    (∀ a, e (chartScalar W a) = algebraMap F W.toAffine.CoordinateRing a) ∧
    e (xOverZ W.toProjective) = affineX W ∧
    e (yOverZ W.toProjective) = affineY W := by
  obtain ⟨f, hf, hc, hm⟩ := exists_zChartAway_equiv_coordinateRing W.toProjective
  refine ⟨RingEquiv.ofBijective f hf, fun a => RingHom.congr_fun hc a, ?_, ?_⟩
  · have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) F) ∈
        MvPolynomial.homogeneousSubmodule (Fin 3) F (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X F (0 : Fin 3))
    have h := hm 1 (MvPolynomial.X 0) hb
    change f (xOverZ W.toProjective) = _ at h
    change f (xOverZ W.toProjective) = Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)
    simpa only [MvPolynomial.aeval_X, Matrix.cons_val_zero] using h
  · have hb : (MvPolynomial.X 1 : MvPolynomial (Fin 3) F) ∈
        MvPolynomial.homogeneousSubmodule (Fin 3) F (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X F (1 : Fin 3))
    have h := hm 1 (MvPolynomial.X 1) hb
    change f (yOverZ W.toProjective) = _ at h
    change f (yOverZ W.toProjective) = Ideal.Quotient.mk _ Polynomial.X
    simpa only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero] using h

abbrev Evaluation := ∀ (L : Type u) [Field L] [DecidableEq L] [Algebra F L],
  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W) ≃
    (W.toProjective.baseChange L).toAffine.Point

variable (G : Law F W) (ev : Evaluation W)

lemma evaluation_one (hev : IsPointsEval W.toProjective G ev)
    (L : Type u) [Field L] [DecidableEq L] [Algebra F L] :
    ev L (G.one (Spec.map (CommRingCat.ofHom (algebraMap F L)))) = 0 := by
  have H := hev.1 L (G.one _) (G.one _)
  change ev L (G.mul _ (G.one _) (G.one _)) = _ at H
  rw [G.one_mul] at H
  exact (add_left_cancel ((add_zero _).trans H)).symm

lemma evaluation_nsmul (hev : IsPointsEval W.toProjective G ev)
    (L : Type u) [Field L] [DecidableEq L] [Algebra F L]
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W))
    (n : ℕ) : ev L (G.nsmul _ n P) = n • ev L P := by
  induction n with
  | zero => simpa only [G.nsmul_zero, zero_smul] using evaluation_one W G ev hev L
  | succ n ih =>
    rw [G.nsmul_succ]
    have H := hev.1 L (G.nsmul _ n P) P
    change ev L (G.mul _ (G.nsmul _ n P) P) = ev L (G.nsmul _ n P) + ev L P at H
    rw [H, ih, succ_nsmul]


def HasCoordinates : Prop :=
  ∀ (L : Type u) [Field L] [DecidableEq L] [Algebra F L]
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W))
    (χ : ZChartRing W.toProjective →+* L),
    P.val = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective →
    ∃ hxy : (W.toProjective.baseChange L).toAffine.Nonsingular
      (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
      ev L P = WeierstrassCurve.Affine.Point.some _ _ hxy

lemma coordinate_evaluation_exists [W.IsElliptic] (hG : IsOriginLaw F W G) :
    ∃ ev : Evaluation W, IsPointsEval W.toProjective G ev ∧ HasCoordinates W ev := by
  have ho : (G.one (𝟙 _)).val = (kwZeroSect F W).val := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  obtain ⟨ev, hev, _, hcoord⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G ho
  exact ⟨ev, hev, hcoord⟩

lemma chart_torsion_iff [W.IsElliptic]
    (hev : IsPointsEval W.toProjective G ev) (hcoord : HasCoordinates W ev)
    (L : Type u) [Field L] [DecidableEq L] [Algebra F L]
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W))
    (χ : ZChartRing W.toProjective →+* L)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective)
    {c : ℕ} (ho : Odd c) :
    G.nsmul _ c P = G.one _ ↔
      (((W.toProjective.baseChange L).toAffine).preΨ' c).eval
        (χ (xOverZ W.toProjective)) = 0 := by
  letI : (W.toProjective.baseChange L).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  obtain ⟨hxy, hpoint⟩ := hcoord L P χ hP
  rw [← (ev L).injective.eq_iff, evaluation_nsmul W G ev hev L P c,
    evaluation_one W G ev hev L, hpoint]
  exact WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi _ ho hxy

lemma chart_support [W.IsElliptic] (hG : IsOriginLaw F W G)
    (hev : IsPointsEval W.toProjective G ev) (hcoord : HasCoordinates W ev)
    (e : ZChartRing W.toProjective ≃+* W.toAffine.CoordinateRing)
    (hscalar : ∀ a, e (chartScalar W a) = algebraMap F W.toAffine.CoordinateRing a)
    (hx : e (xOverZ W.toProjective) = affineX W)
    (z : Spec (CommRingCat.of W.toAffine.CoordinateRing))
    {c : ℕ} (ho : Odd c) :
    affineResidueMap z (divisionElement W c) = 0 ↔
      G.schemeNsmul c ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W.toProjective) z) =
        originPoint F W := by
  classical
  let L := (Spec (CommRingCat.of W.toAffine.CoordinateRing)).residueField z
  let σ : W.toAffine.CoordinateRing →+* L := affineResidueMap z
  let τ := σ.comp (algebraMap F W.toAffine.CoordinateRing)
  letI : Algebra F L := τ.toAlgebra
  let χ := σ.comp e.toRingHom
  have hχ : χ.comp (chartScalar W) = τ := by
    ext a
    exact congrArg σ (hscalar a)
  let P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W) :=
    ⟨Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective, by
      rw [Category.assoc, chart_structure, ← Spec.map_comp]
      exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hχ⟩
  have hz : Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint L) = z := by
    rw [show σ = affineResidueMap z from rfl, affineResidueMap_spec]
    exact Scheme.fromSpecResidueField_apply _ _
  have hP : P.val (IsLocalRing.closedPoint L) =
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W.toProjective) z := by
    change (Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective) _ = _
    rw [show CommRingCat.ofHom χ = CommRingCat.ofHom e.toRingHom ≫
      CommRingCat.ofHom σ from rfl, Spec.map_comp]
    simp only [Scheme.Hom.comp_apply, hz]
  have hpol : (((W.toProjective.baseChange L).toAffine).preΨ' c).eval
      (χ (xOverZ W.toProjective)) = σ (divisionElement W c) := by
    change (((W.map τ).preΨ' c).eval (σ (e (xOverZ W.toProjective)))) = _
    rw [hx, WeierstrassCurve.map_preΨ', Polynomial.eval_map]
    exact (divisionElement_eval W c σ).symm
  have hpoly := chart_torsion_iff W G ev hev hcoord L P χ rfl ho
  rw [hpol] at hpoly
  have hpoint := field_point_torsion_iff G _ P c
  rw [hP] at hpoint
  have hone : (G.one (𝟙 _)).val = origin F W := by
    simpa only [Category.id_comp, origin] using hG.1 (𝟙 _)
  rw [hone] at hpoint
  exact hpoly.symm.trans hpoint


lemma kernel_rank [CharZero F] [W.IsElliptic]
    (hev : IsPointsEval W.toProjective G ev)
    (n : ℕ) (hn : 0 < n) [IsFinite (G.schemeNsmul n)] [Etale (G.schemeNsmul n)] :
    ∀ z, (G.schemeKerStr n).finrank z = n^2 := by
  classical
  let L := AlgebraicClosure F
  letI : CharZero L := Algebra.charZero_of_charZero F L
  letI : (W.toProjective.baseChange L).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange W
  let t := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let e : SchemeHomOver t (G.schemeKerStr n) ≃
      Submodule.torsionBy ℤ (W.toProjective.baseChange L).toAffine.Point (n : ℤ) :=
    (kernelPointsEquiv G t n).trans (Equiv.subtypeEquiv (ev L) (by
      intro z
      rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
      rw [← evaluation_nsmul W G ev hev L z n, ← evaluation_one W G ev hev L]
      exact (ev L).injective.eq_iff.symm))
  intro z
  have hz : z = t (IsLocalRing.closedPoint L) := Subsingleton.elim _ _
  have hcount := finrank_eq_natCard_of_isFinite_of_etale_of_isAlgClosed
    (G.schemeKerStr n) L (algebraMap F L)
  apply (congrArg (G.schemeKerStr n).finrank hz).trans
  apply hcount.trans
  exact (Nat.card_congr e).trans
    (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
      (W.toProjective.baseChange L).toAffine
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (by norm_num))

open P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain.WeierstrassProjModel

lemma field_point_chart_or_origin
    (L : Type u) [Field L] [Algebra F L]
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W)) :
    Set.range P.val ⊆ Set.range (zChartι W.toProjective) ∨
      P.val = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ origin F W := by
  classical
  obtain ⟨i, ψ, hfac⟩ := kw_lrApt_schemeHom_factor W L P
  by_cases hz : ψ (kw_lrChart_gen W i 2) ≠ 0
  · left
    rw [hfac]
    exact kw_lrApt_range_subset_of_gen_ne_zero W L ψ 2 hz
  · right
    have hz' : ψ (kw_lrChart_gen W i 2) = 0 := not_ne_iff.mp hz
    let O : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ origin F W, by
        rw [Category.assoc, show origin F W ≫ structureMap F W = 𝟙 _ from (kwZeroSect F W).property,
          Category.comp_id]⟩
    have hO : O.val = Spec.map (CommRingCat.ofHom ((algebraMap F L).comp (kwYChartEval F W))) ≫
        (projModelAffineOpenCoverCR F W.toProjective).openCover.f (1 : Fin 3) := by
      change Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ (Spec.map (CommRingCat.ofHom (kwYChartEval F W)) ≫ _) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    let ψO := ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.algHomOfFac W L O 1 _ hO
    have hvec : kw_lrApt_chartEval W L 1 ψO = ![(0 : L), 1, 0] := by
      funext k
      change (algebraMap F L) (kwYChartEval F W (kw_lrChart_gen W 1 k)) = _
      rw [kwYChartEval_gen_eq]
      fin_cases k <;> simp
    have heq : P = O := by
      apply kw_lrApt_toPointClass_injective W L
      rw [kw_lrApt_toPointClass_eq_of_fac W L P i ψ hfac,
        kw_lrApt_toPointClass_eq_of_fac W L O 1 ψO hO, hvec]
      exact ProjWeierstrassDehomog.pointClass_eq_pointAtInfinity
        (kw_lrApt_chartEval_equation W L i ψ) hz' (kw_lrApt_chartEval_ne_zero W L i ψ)
    exact congrArg Subtype.val heq

lemma chart_covers (x : Curve F W) (hx : x ≠ originPoint F W) :
    x ∈ Set.range (zChartι W.toProjective) := by
  let L := (Curve F W).residueField x
  let τ := ArithmeticThetaCurveDegree.baseToResidue F (structureMap F W) x
  letI : Algebra F L := τ.toAlgebra
  let P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F L))) (structureMap F W) :=
    ⟨(Curve F W).fromSpecResidueField x,
      (ArithmeticThetaCurveDegree.specMap_baseToResidue (Curve F W) F (structureMap F W) x).symm⟩
  rcases field_point_chart_or_origin W L P with hc | ho
  · apply hc
    exact ⟨IsLocalRing.closedPoint L, Scheme.fromSpecResidueField_apply _ _⟩
  · apply (hx _).elim
    have h := congrArg (fun f : Spec (CommRingCat.of L) ⟶ Curve F W =>
      f (IsLocalRing.closedPoint L)) ho
    change (Curve F W).fromSpecResidueField x _ = _ at h
    rw [Scheme.fromSpecResidueField_apply, Scheme.Hom.comp_apply] at h
    exact h.trans (congrArg (origin F W) (Subsingleton.elim _ _))

end Principality

open CategoryTheory AlgebraicGeometry NeronModelInfra
open Principality
open ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart
open ArithmeticThetaGeometricNormR0150
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

/-- The inverse odd division polynomial has the Kato divisor on the actual
projective curve over the original field, at every scheme point. -/
theorem general_kato_principality :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic]
  (G : Law F W) (hG : IsOriginLaw F W G)
  [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)],
  ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 →
    ∃ g : (Curve F W).functionField, HasKatoDivisor F W G c g := by
  intro F _ _ W _ G hG _ _ c hc hcop
  classical
  letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
    projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap F W) := projModelStrCR_isProper W.toProjective
  have hcpos : 0 < c := lt_trans Nat.zero_lt_one hc
  have ho := odd_of_coprime_six hcop
  obtain ⟨e, hscalar, hx, _⟩ := exists_chart_equiv W
  obtain ⟨ev, hev, hcoord⟩ := coordinate_evaluation_exists W G hG
  let j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ Curve F W :=
    (specIso e).hom ≫ zChartι W.toProjective
  let g := chartCandidate W j c
  have hg : g ≠ 0 := chartCandidate_ne_zero W j hcpos
  letI : Etale (G.schemeNsmul c) := etale_nsmul G hG.2 c hcpos
  letI : IsProper (G.schemeNsmul c) :=
    MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated)
      (G.schemeNsmul c) (structureMap F W) inferInstance
      (by rw [G.schemeNsmul_over]; infer_instance)
  letI : LocallyQuasiFinite (G.schemeNsmul c) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  letI : IsFinite (G.schemeNsmul c) := .of_isProper_of_locallyQuasiFinite _
  have hrank : ∀ z, (G.schemeNsmul c).finrank z = c^2 :=
    rank_from_identity G c (c^2) (Principality.kernel_rank W G ev hev c hcpos)
  letI : Surjective (G.schemeNsmul c) := (G.schemeNsmul c).one_le_finrank_iff_surjective.mp (by
    intro z
    rw [hrank]
    exact Nat.one_le_pow 2 c hcpos)
  have hone : (G.one (𝟙 _)).val = origin F W := by
    simpa only [Category.id_comp] using hG.1 (𝟙 _)
  have hfix : G.schemeNsmul c (originPoint F W) = originPoint F W := by
    have h := congrArg (fun f : Spec (CommRingCat.of F) ⟶ Curve F W =>
      f (IsLocalRing.closedPoint F)) (CoprimeTorsion.one_mul_map G c)
    rw [hone] at h
    exact h
  have hoff : ∀ x, x ≠ originPoint F W →
      Scheme.ord g x = -(if G.schemeNsmul c x = originPoint F W then 1 else 0) := by
    intro x hxo
    by_cases hgen : x = _root_.genericPoint (Curve F W)
    · subst x
      rw [NormOrders.ord_generic (X := Curve F W),
        NormOrders.map_generic (X := Curve F W) (Y := Curve F W), if_neg hxo, neg_zero]
    · obtain ⟨z₀, hz₀⟩ := chart_covers W x hxo
      let z := (specIso e).inv z₀
      have hz : j z = x := by
        change zChartι W.toProjective ((specIso e).hom ((specIso e).inv z₀)) = x
        rw [show (specIso e).hom ((specIso e).inv z₀) = z₀ from
          congrArg (fun f : Spec (CommRingCat.of (ZChartRing W.toProjective)) ⟶ _ => f z₀)
            (specIso e).inv_hom_id]
        exact hz₀
      have hzU : j z ∈ j ''ᵁ (⊤ : (Spec (CommRingCat.of W.toAffine.CoordinateRing)).Opens) :=
        ⟨z, trivial, rfl⟩
      letI : Nonempty (j ''ᵁ ⊤ : (Curve F W).Opens) := ⟨⟨j z, hzU⟩⟩
      have hco : Order.coheight (j z) = 1 := by
        rw [hz]
        exact NormOrders.smooth_coheight_one_of_ne_generic F (structureMap F W) x hgen
      have hord := chartCandidate_order (X := Curve F W) W (structureMap F W) j
        hcpos ho ⟨j z, hzU⟩ hco
      have hsupport := (chartSection_evaluation_zero_iff j z hzU (divisionElement W c)).trans
        (chart_support W G ev hG hev hcoord e hscalar hx z ho)
      change (Curve F W).evaluation (j ''ᵁ ⊤) (j z) hzU
        (chartDivisionSection W j c) = 0 ↔ G.schemeNsmul c (j z) = originPoint F W at hsupport
      change Scheme.ord (chartCandidate W j c) x = _
      rw [← hz, ← hsupport]
      exact hord
  have hall := divisor_from_off_origin (structureMap F W) (origin F W)
    (kwZeroSect F W).property (G.schemeNsmul c) (G.schemeNsmul_over c) hfix g hg hoff
  refine ⟨g, hg, ?_⟩
  intro x
  simpa only [katoOrder, originPoint, hrank, Nat.cast_pow] using hall x

end ArithmeticThetaGeneralEllipticKatoR0168
#print axioms ArithmeticThetaGeneralEllipticKatoR0168.general_kato_principality

