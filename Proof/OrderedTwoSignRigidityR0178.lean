module

public import CompatibleLevelDefinitionsR0178
public import OrderedLegendreParameterRigidityR0177
public import StandardLegendreTwoMarkingR0177
public import FullLevelFreeSignR0176

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaCompatibleLevelR0178
namespace OrderedTwoSignRigidity
open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaLegendreComparisonR0177.OrderedLegendreParameterRigidity
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts

lemma local_chart_sign {R : Type u} [Field R]
    (W : WeierstrassCurve R)
    (p0 p1 : Base R ⟶ Curve R W)
    (hp0 : HasCoordinates R W p0 0 0)
    (hp1 : HasCoordinates R W p1 1 0)
    (f : Curve R W ≅ Curve R W)
    (hf : f.hom ≫ structureMap R W = structureMap R W)
    (ho : origin R W ≫ f.hom = origin R W)
    (h0 : p0 ≫ f.hom = p0) (h1 : p1 ≫ f.hom = p1) :
    ∃ e : ChartRing R W ≃+* ChartRing R W,
      (∀ t, e (scalar W t) = scalar W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartInclusion R W =
        chartInclusion R W ≫ f.hom ∧
      e (xOverZ W.toProjective) = xOverZ W.toProjective ∧
      (e (yOverZ W.toProjective) = yOverZ W.toProjective ∨
       e (yOverZ W.toProjective) = -yOverZ W.toProjective) := by
  obtain ⟨e, hec, hei⟩ := ChartEquiv.solution R W W f hf ho
  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := exists_ringHom_originChartRing_powerSeries W
  obtain ⟨l, hlc, hlx, hly, hF2, hF3⟩ := LaurentFiltration.solution R W Φ hΦc hΦx hΦz
  obtain ⟨hx1, hx2, hy1, hy2⟩ := LaurentCoeff.solution R W W f hf ho
    e.toRingHom hei Φ hΦc hΦx hΦz l hlc hlx hly
  obtain ⟨a, b, r, s, t, hx, hy⟩ := VariableChange.WMLocal.triangular_of_coeff
    (scalar W) (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ W.toProjective) (yOverZ W.toProjective) e.toRingHom l
    hF2 hF3 hx1 hx2 hy1 hy2
  obtain ⟨hp0o, χ0, rfl, χ0x, χ0y⟩ := hp0
  obtain ⟨hp1o, χ1, rfl, χ1x, χ1y⟩ := hp1
  have hc0 := evaluation_scalar W χ0 hp0o
  have hc1 := evaluation_scalar W χ1 hp1o
  have hχ0 := evaluation_comp W W f.hom e.toRingHom hei χ0 χ0 h0
  have hχ1 := evaluation_comp W W f.hom e.toRingHom hei χ1 χ1 h1
  have ev0 (z : ChartRing R W) : χ0 (e z) = χ0 z := RingHom.congr_fun hχ0 z
  have ev1 (z : ChartRing R W) : χ1 (e z) = χ1 z := RingHom.congr_fun hχ1 z
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx hy
  have hr : r = 0 := by
    have h := congrArg χ0 hx
    simpa only [ev0, χ0x, map_add, map_mul, hc0, χ0x, mul_zero, zero_add] using h.symm
  have ha : (a : R) = 1 := by
    have h := congrArg χ1 hx
    simpa only [ev1, χ1x, map_add, map_mul, hc1, χ1x, mul_one, hr, add_zero] using h.symm
  have ht : t = 0 := by
    have h := congrArg χ0 hy
    simpa only [ev0, χ0y, map_add, map_mul, hc0, χ0x, χ0y, mul_zero, zero_add] using h.symm
  have hs : s = 0 := by
    have h := congrArg χ1 hy
    simpa only [ev1, χ1y, map_add, map_mul, hc1, χ1x, χ1y, mul_zero, mul_one,
      zero_add, ht, add_zero] using h.symm
  have ha' : a = 1 := Units.ext ha
  subst a
  obtain ⟨g, gx, gy⟩ := VariableChange.WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv
    W W e hec 1 b r s t hx hy
  simp only [hr, hs, ht, inv_one, Units.val_one, one_smul, mul_zero, neg_zero,
    sub_self, map_zero, add_zero] at gx gy
  obtain ⟨C, hC, hu, hCr, hCs, hCt⟩ := Triangular.solution R W W g 1 b⁻¹ 0 0 0
    (by simpa using gx) (by simpa using gy)
  have hu1 : (C.u : R)^2 = 1 := by simpa using hu.1
  have hc : C.u = 1 ∨ C.u = -1 := by
    rcases sq_eq_one_iff.mp hu1 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  have hbx : e (xOverZ W.toProjective) = xOverZ W.toProjective := by
    simpa [hr] using hx
  refine ⟨e, hec, hei, hbx, ?_⟩
  rcases hc with hc | hc
  · have hb : b = 1 := by
      apply inv_injective
      apply Units.ext
      simpa [hc, pow_succ, pow_zero] using hu.2.symm
    exact Or.inl (by simpa [hb, hs, ht, neg_one_mul] using hy)
  · have hb : b = -1 := by
      apply inv_injective
      apply Units.ext
      simpa [hc, pow_succ, pow_zero] using hu.2.symm
    have hb' : (b : R) = -1 := congrArg Units.val hb
    rw [hb', hs, ht, map_neg, map_one, map_zero, zero_mul, add_zero, add_zero] at hy
    exact Or.inr (hy.trans (by ring))

open NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176.FullLevelFreeSignR0176

lemma inversion_over {R : Type u} [CommRing R] (W : WeierstrassCurve R) (G : Law R W) :
    inversion R W G ≫ structureMap R W = structureMap R W :=
  (G.inv _ _).property

lemma comp_inversion {R : Type u} [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
    {T : Scheme.{u}} (t : T ⟶ Base R) (P : SchemeHomOver t (structureMap R W)) :
    P.val ≫ inversion R W G = (G.inv t P).val := by
  have h := congrArg Subtype.val (inverse_natural G (structureMap R W) t P.val P.property
    ⟨𝟙 _, Category.id_comp _⟩)
  simpa only [inversion, WeierstrassProjModel.schemeHomOverComp, Category.comp_id] using h

lemma chart_negative_is_inversion {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    [IsReduced (Curve R W)] [Scheme.IsSeparated (Curve R W)]
    (hW1 : W.a₁ = 0) (hW3 : W.a₃ = 0)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (f : Curve R W ⟶ Curve R W) (hf : f ≫ structureMap R W = structureMap R W)
    (e : ChartRing R W →+* ChartRing R W)
    (he : Spec.map (CommRingCat.ofHom e) ≫ chartInclusion R W = chartInclusion R W ≫ f)
    (hx : e (xOverZ W.toProjective) = xOverZ W.toProjective)
    (hy : e (yOverZ W.toProjective) = -yOverZ W.toProjective) :
    f = inversion R W G := by
  classical
  let Z := Spec (CommRingCat.of (ChartRing R W))
  letI : IsReduced Z := isReduced_of_isOpenImmersion (chartInclusion R W)
  letI : IsProper (structureMap R W) := projModelStrCR_isProper W.toProjective
  apply ChartExt.solution R W
  apply ext_of_fromSpecResidueField_eq _ _ (structureMap R W) Set.univ dense_univ
  · intro z _
    let F := Z.residueField z
    let q := Z.fromSpecResidueField z
    let χ : ChartRing R W →+* F := (Spec.preimage q).hom
    have hχ : Spec.map (CommRingCat.ofHom χ) = q := Spec.map_preimage q
    let σ := χ.comp (scalar W)
    letI : Algebra R F := σ.toAlgebra
    let t := Spec.map (CommRingCat.ofHom (algebraMap R F))
    let P : SchemeHomOver t (structureMap R W) := ⟨q ≫ chartInclusion R W, by
      rw [Category.assoc, chart_structure, ← hχ, ← Spec.map_comp]
      rfl⟩
    let Q : SchemeHomOver t (structureMap R W) := ⟨P.val ≫ f, by
      rw [Category.assoc, hf]; exact P.property⟩
    obtain ⟨ev, hev, _, hcoord⟩ :=
      ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
        (by simpa only [origin, Category.id_comp] using hG.1 (𝟙 (Base R)))
    have hz : ev F (G.one t) = 0 := by
      have h := hev.1 F (G.one t) (G.one t)
      rw [G.one_mul] at h
      exact (add_left_cancel ((add_zero _).trans h)).symm
    have hn : ev F (G.inv t P) = -(ev F P) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← hev.1 F, G.inv_mul_cancel, hz]
    obtain ⟨hxy, hP⟩ := hcoord F P χ (by exact congrArg (fun a => a ≫ chartInclusion R W) hχ.symm)
    have hQfac : Q.val = Spec.map (CommRingCat.ofHom (χ.comp e)) ≫ chartInclusion R W := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, he, hχ]
      rfl
    obtain ⟨hxyQ, hQ⟩ := hcoord F Q (χ.comp e) hQfac
    have hQP : Q = G.inv t P := by
      apply (ev F).injective
      rw [hQ, hn, hP, WeierstrassCurve.Affine.Point.neg_some]
      congr 1
      · simp only [RingHom.comp_apply, hx]
      · change χ (e (yOverZ W.toProjective)) = -χ (yOverZ W.toProjective) -
          algebraMap R F W.a₁ * χ (xOverZ W.toProjective) - algebraMap R F W.a₃
        simp only [hy, map_neg, hW1, hW3, map_zero, zero_mul, sub_zero]
    have hval := congrArg Subtype.val hQP
    change (q ≫ chartInclusion R W) ≫ f = _ at hval
    rw [← comp_inversion W G t P] at hval
    exact hval
  · simp only [Category.assoc, hf, inversion_over]

lemma chart_positive_is_identity {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [Scheme.IsSeparated (Curve R W)]
    (f : Curve R W ⟶ Curve R W) (e : ChartRing R W ≃+* ChartRing R W)
    (hc : ∀ t, e (scalar W t) = scalar W t)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartInclusion R W = chartInclusion R W ≫ f)
    (hx : e (xOverZ W.toProjective) = xOverZ W.toProjective)
    (hy : e (yOverZ W.toProjective) = yOverZ W.toProjective) : f = 𝟙 _ := by
  have hid : e.toRingHom = RingHom.id _ :=
    LaurentFiltration.WMLocal.zChart_ringHom_ext W _ _ (RingHom.ext hc) hx hy
  apply ChartExt.solution R W
  change chartInclusion R W ≫ f = chartInclusion R W ≫ 𝟙 _
  rw [← he, hid]
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

end OrderedTwoSignRigidity

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaLegendreComparisonR0177.OrderedLegendreParameterRigidity
open OrderedTwoSignRigidity

theorem ordered_two_sign_rigidity :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (lam : R), IsUnit (lam * (lam - 1)) → ∀ (G : ArithmeticThetaRelativeKatoR0169.Law R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) G → ∀ (p0 p1 : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam))), ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p0 0 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p1 1 0 → ∀ f : CategoryTheory.Iso (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)), CategoryTheory.CategoryStruct.comp f.hom (ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) = ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) → CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) f.hom = ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) → CategoryTheory.CategoryStruct.comp p0 f.hom = p0 → CategoryTheory.CategoryStruct.comp p1 f.hom = p1 → f.hom = CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) ∨ f.hom = ArithmeticThetaCompatibleLevelR0178.inversion R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) G := by
  intro R _ _ _ _ _ lam hlam G hG p0 p1 hp0 hp1 f hf ho h0 h1
  let W := legendreAt R lam
  letI : W.IsElliptic := (standard_legendre_two_marking R lam hlam).1
  have hg := relative_curve_geometry R W
  letI := hg.1
  letI := hg.2.1
  letI := hg.2.2.2.1
  letI := hg.2.2.2.2.1
  letI : IsProper (structureMap R W) := projModelStrCR_isProper W.toProjective
  let K := FractionRing R
  let σ := algebraMap R K
  let Wk := W.map σ
  obtain ⟨φ, hφ, hc⟩ := exists_isCoefficientHom W.toProjective σ
  let b := Proj.map φ hφ
  let ι := Spec.map (CommRingCat.ofHom σ)
  have hb : IsPullback b (structureMap K Wk) (structureMap R W) ι :=
    isPullback_projMap_of_isCoefficientHom W.toProjective σ φ hφ hc
  obtain ⟨fk, hfko, hfk⟩ := cartesian_iso (structureMap R W) (structureMap R W)
    (structureMap K Wk) (structureMap K Wk) ι b b hb hb f hf
  obtain ⟨pk0, hpk0, ep0⟩ := coefficient_coordinates W σ φ hφ hc p0 0 0 hp0
  obtain ⟨pk1, hpk1, ep1⟩ := coefficient_coordinates W σ φ hφ hc p1 1 0 hp1
  have eo : origin K Wk ≫ b = ι ≫ origin R W :=
    coefficient_origin W σ φ hφ hc
  have hko : origin K Wk ≫ fk.hom = origin K Wk := by
    apply hb.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, eo, Category.assoc, ho]
    · rw [Category.assoc, hfko]
  have hk0 : pk0 ≫ fk.hom = pk0 := by
    apply hb.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, ep0, Category.assoc, h0]
    · rw [Category.assoc, hfko]
  have hk1 : pk1 ≫ fk.hom = pk1 := by
    apply hb.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, ep1, Category.assoc, h1]
    · rw [Category.assoc, hfko]
  obtain ⟨e, hec, hei, hex, hey⟩ := local_chart_sign Wk pk0 pk1
    (by simpa only [map_zero] using hpk0) (by simpa only [map_zero, map_one] using hpk1)
    fk hfko hko hk0 hk1
  obtain ⟨H, hm, hone⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    σ (structureMap R W) (structureMap K Wk) b hb G
  have hH : IsOriginLaw K Wk H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [hone, hG.1, Category.assoc, eo]
        rfl
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z) (kwZeroSect K Wk).property).trans
            (Category.comp_id t)).symm)
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hinv : inversion K Wk H ≫ b = b ≫ inversion R W G := by
    let t := structureMap K Wk
    letI := H.pointGroup t
    letI := G.pointGroup (t ≫ ι)
    let m : SchemeHomOver t (structureMap K Wk) →*
        SchemeHomOver (t ≫ ι) (structureMap R W) := {
      toFun := fun x => ⟨x.val ≫ b, by rw [Category.assoc, hb.w, ← Category.assoc, x.property]⟩
      map_one' := Subtype.ext (hone t)
      map_mul' := fun x y => Subtype.ext (hm t x y) }
    have h := congrArg Subtype.val (map_inv m (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver t (structureMap K Wk)))
    have hn := comp_inversion W G (t ≫ ι) ⟨b, hb.w⟩
    change (H.inv t ⟨𝟙 _, Category.id_comp _⟩).val ≫ b =
      (G.inv (t ≫ ι) ⟨b, hb.w⟩).val at h
    exact h.trans hn.symm
  letI : Flat ι := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  letI : Flat b := MorphismProperty.of_isPullback (P := @Flat) hb.flip inferInstance
  letI : IsDominant b := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure (Curve R W)]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr ⟨genericPoint (Curve K Wk),
      GenericComparisonProof.generic_eq_of_flat b⟩
  letI : IsProper (structureMap K Wk) := projModelStrCR_isProper Wk.toProjective
  letI : Scheme.IsSeparated (Curve K Wk) := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from (structureMap K Wk)]
    infer_instance
  rcases hey with hey | hey
  · left
    have hid := chart_positive_is_identity Wk fk.hom e hec hei hex hey
    apply ext_of_isDominant_of_isSeparated (structureMap R W) (by
      rw [Category.id_comp]
      exact hf) b
    rw [← hfk, hid, Category.id_comp, Category.comp_id]
  · right
    have hi := chart_negative_is_inversion Wk (by simp [Wk, W, legendreAt])
      (by simp [Wk, W, legendreAt]) H hH fk.hom hfko e.toRingHom hei hex hey
    apply ext_of_isDominant_of_isSeparated (structureMap R W)
      (hf.trans (inversion_over W G).symm) b
    rw [← hfk, hi, hinv]

#print axioms ordered_two_sign_rigidity
end ArithmeticThetaCompatibleLevelR0178
