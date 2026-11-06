import LegendreComparisonDefinitionsR0177
import RelativeCurveGeometryR0169
import ProjectivePointsEvaluationR0146
import FullLevelRepresentabilityR0175
import FullLevelCoverGeometryR0175
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177.StandardMarking
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra
variable {R : Type u} [CommRing R]

/-- Evaluate the affine coordinate ring and use the actual projective chart inclusion. -/
theorem exists_coordinate_section (W : WeierstrassCurve R) (x y : R)
    (hxy : W.toAffine.Equation x y) :
    ∃ P : Base R ⟶ Curve R W, HasCoordinates R W P x y := by
  obtain ⟨f, hf, hcomp, hgen⟩ := exists_zChartAway_equiv_coordinateRing W.toProjective
  let ev : Polynomial (Polynomial R) →+* R :=
    (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))
  have hev : ev W.toAffine.polynomial = 0 := by
    change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) W.toAffine.polynomial) = 0
    rw [Polynomial.eval_map]
    rw [Polynomial.eval₂_evalRingHom]
    exact hxy
  let q : (Polynomial (Polynomial R) ⧸ Ideal.span {W.toAffine.polynomial}) →+* R :=
    Ideal.Quotient.lift _ ev (by
      intro p hp
      exact (Ideal.span_le.mpr (show {W.toAffine.polynomial} ⊆ (RingHom.ker ev : Set _) from
        Set.singleton_subset_iff.mpr hev)) hp)
  let χ : ChartRing R W →+* R := q.comp f
  have hx : χ (xOverZ W.toProjective) = x := by
    have h := hgen 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X R 0))
    change q (f (xOverZ W.toProjective)) = x
    change f (xOverZ W.toProjective) = _ at h
    rw [h]
    simp [q, ev]
  have hy : χ (yOverZ W.toProjective) = y := by
    have h := hgen 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X R 1))
    change q (f (yOverZ W.toProjective)) = y
    change f (yOverZ W.toProjective) = _ at h
    rw [h]
    simp [q, ev]
  have hc : χ.comp (algebraMap R (ChartRing R W)) = RingHom.id R := by
    change q.comp (f.comp _) = _
    change f.comp (algebraMap R (ChartRing R W)) = _ at hcomp
    rw [hcomp]
    ext r
    change ev (Polynomial.C (Polynomial.C r)) = r
    simp [ev]
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W, ?_, χ, rfl, hx, hy⟩
  change (Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective) ≫
    projModelStrCR W.toProjective = _
  rw [Category.assoc, show zChartι W.toProjective ≫ projModelStrCR W.toProjective =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R W))) from
        kw_pbac_awayι_comp_projModelStrCR R W.toProjective 2,
    ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (χ.comp (algebraMap R (ChartRing R W)))) = _
  rw [hc]
  exact Spec.map_id _

abbrev fieldSection (W : WeierstrassCurve R)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (F : Type u) [Field F] [Algebra R F] :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (structureMap R W) :=
  schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap R F))) (Category.comp_id _) P

theorem fieldSection_fac (W : WeierstrassCurve R)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) (x y : R)
    (hP : HasCoordinates R W P.val x y)
    (F : Type u) [Field F] [Algebra R F] :
    ∃ χ : ChartRing R W →+* F,
      (fieldSection W P F).val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
      χ (xOverZ W.toProjective) = algebraMap R F x ∧
      χ (yOverZ W.toProjective) = algebraMap R F y := by
  obtain ⟨_, χ, he, hx, hy⟩ := hP
  refine ⟨(algebraMap R F).comp χ, ?_, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ P.val = _
    rw [he, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · simp [hx]
  · simp [hy]

/-- Separatedness descends equality of sections from the fraction field. -/
theorem section_ext_fraction [IsDomain R] (W : WeierstrassCurve R)
    (P Q : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (h : fieldSection W P (FractionRing R) = fieldSection W Q (FractionRing R)) : P = Q := by
  let f := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  letI : IsSeparated (structureMap R W) := by
    change IsSeparated (projModelStrCR W.toProjective)
    unfold projModelStrCR
    infer_instance
  letI : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap f)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot f).mp hf]
    exact bot_le
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated (structureMap R W) (P.property.trans Q.property.symm)
    (Spec.map (CommRingCat.ofHom f)) (congrArg Subtype.val h)

/-- An affine-chart section avoids the origin on every residue field, hence on the base. -/
theorem coordinate_section_avoids [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) (x y : R)
    (hP : HasCoordinates R W P.val x y) :
    Disjoint (Set.range P.val) (Set.range (origin R W)) := by
  classical
  obtain ⟨ev, hev, he0, hec⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by change (G.one (𝟙 _)).val = origin R W
          simpa only [Category.id_comp] using hG.1 (𝟙 _))
  have hn : ∀ (F : Type u) [Field F] [Algebra R F],
      fieldSection W P F ≠ G.one (Spec.map (CommRingCat.ofHom (algebraMap R F))) := by
    intro F _ _ hh
    obtain ⟨χ, hχ, _, _⟩ := fieldSection_fac W P x y hP F
    obtain ⟨hns, he⟩ := hec F (fieldSection W P F) χ hχ
    have hz : ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) = 0 := by
      convert he0 F using 2
      apply Subtype.ext
      exact hG.1 _
    rw [hh, hz] at he
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns he.symm
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ hz
  let F := (Base R).residueField p
  let t := (Base R).fromSpecResidueField p
  let φ : R →+* F := (Spec.preimage t).hom
  letI : Algebra R F := φ.toAlgebra
  have ht : Spec.map (CommRingCat.ofHom (algebraMap R F)) = t := Spec.map_preimage t
  have hd := (ArithmeticThetaFullLevelCoverR0175.CoverGeometryR0175.field_avoids_iff hG
    (Spec.map (CommRingCat.ofHom (algebraMap R F))) (fieldSection W P F)).mpr (hn F)
  apply Set.disjoint_left.mp hd _ hz
  refine ⟨IsLocalRing.closedPoint F, ?_⟩
  change P.val ((Spec.map (CommRingCat.ofHom (algebraMap R F))) _) = P.val p
  rw [ht]
  exact congrArg P.val (Scheme.fromSpecResidueField_apply p _)


/-- Compute the two doubles and labeled sum in the fraction field, then descend. -/
theorem legendre_coordinates_relations [IsDomain R] [IsNoetherianRing R]
    (lam : R) [(legendreAt R lam).IsElliptic]
    (G : Law R (legendreAt R lam)) (hG : IsOriginLaw R (legendreAt R lam) G)
    (P Q S : SchemeHomOver (𝟙 (Base R)) (structureMap R (legendreAt R lam)))
    (hP : HasCoordinates R (legendreAt R lam) P.val 0 0)
    (hQ : HasCoordinates R (legendreAt R lam) Q.val 1 0)
    (hS : HasCoordinates R (legendreAt R lam) S.val lam 0) :
    G.nsmul (𝟙 _) 2 P = G.one (𝟙 _) ∧
    G.nsmul (𝟙 _) 2 Q = G.one (𝟙 _) ∧
    G.mul (𝟙 _) P Q = S := by
  classical
  let W := legendreAt R lam
  let F := FractionRing R
  let t := Spec.map (CommRingCat.ofHom (algebraMap R F))
  obtain ⟨ev, hev, he0, hec⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by change (G.one (𝟙 _)).val = origin R W
          simpa only [Category.id_comp] using hG.1 (𝟙 _))
  have hz : ev F (G.one t) = 0 := by
    convert he0 F using 2
    apply Subtype.ext
    exact hG.1 _
  have hp : ∃ h : (W.toProjective.baseChange F).toAffine.Nonsingular 0 0,
      ev F (fieldSection W P F) = WeierstrassCurve.Affine.Point.some 0 0 h := by
    obtain ⟨χ, hc, hx, hy⟩ := fieldSection_fac W P 0 0 hP F
    simpa only [hx, hy, map_zero] using hec F (fieldSection W P F) χ hc
  have hq : ∃ h : (W.toProjective.baseChange F).toAffine.Nonsingular 1 0,
      ev F (fieldSection W Q F) = WeierstrassCurve.Affine.Point.some 1 0 h := by
    obtain ⟨χ, hc, hx, hy⟩ := fieldSection_fac W Q 1 0 hQ F
    simpa only [hx, hy, map_zero, map_one] using hec F (fieldSection W Q F) χ hc
  have hs : ∃ h : (W.toProjective.baseChange F).toAffine.Nonsingular (algebraMap R F lam) 0,
      ev F (fieldSection W S F) = WeierstrassCurve.Affine.Point.some (algebraMap R F lam) 0 h := by
    obtain ⟨χ, hc, hx, hy⟩ := fieldSection_fac W S lam 0 hS F
    simpa only [hx, hy, map_zero] using hec F (fieldSection W S F) χ hc
  obtain ⟨hp, ep⟩ := hp
  obtain ⟨hq, eq⟩ := hq
  obtain ⟨hs, es⟩ := hs
  have hmul (A B : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      fieldSection W (G.mul (𝟙 _) A B) F = G.mul t (fieldSection W A F) (fieldSection W B F) :=
    G.mul_natural _ _ _ (Category.comp_id _) A B
  have hone : fieldSection W (G.one (𝟙 _)) F = G.one t :=
    G.one_natural _ _ _ (Category.comp_id _)
  refine ⟨?_, ?_, ?_⟩
  · rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_one_apply]
    apply section_ext_fraction W
    rw [hmul, hone]
    apply (ev F).injective
    rw [hev.1 F, ep, hz]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [W, legendreAt, WeierstrassCurve.Affine.negY]
  · rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_one_apply]
    apply section_ext_fraction W
    rw [hmul, hone]
    apply (ev F).injective
    rw [hev.1 F, eq, hz]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [W, legendreAt, WeierstrassCurve.Affine.negY]
  · apply section_ext_fraction W
    rw [hmul]
    apply (ev F).injective
    rw [hev.1 F, ep, eq, es, WeierstrassCurve.Affine.Point.add_of_X_ne zero_ne_one]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    simp [W, legendreAt, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    ring

end ArithmeticThetaLegendreComparisonR0177.StandardMarking

namespace ArithmeticThetaLegendreComparisonR0177
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
/-- The canonical ordered full two-torsion marking of the Legendre cubic. -/
theorem standard_legendre_two_marking :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (lam : R), IsUnit (lam * (lam - 1)) → (legendreAt R lam).IsElliptic ∧ ∃ G : Law R (legendreAt R lam), IsOriginLaw R (legendreAt R lam) G ∧ ∃ M : FullLevel R (legendreAt R lam) G 2 (𝟙 (Base R)), HasCoordinates R (legendreAt R lam) M.x.val 0 0 ∧ HasCoordinates R (legendreAt R lam) M.y.val 1 0 ∧ HasCoordinates R (legendreAt R lam) (G.mul (𝟙 (Base R)) M.x M.y).val lam 0 := by
  intro R _ _ _ _ _ lam hlam
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  have h16 : IsUnit (16 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (16 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  have he : (legendreAt R lam).IsElliptic := by
    constructor
    have hΔ : (legendreAt R lam).Δ = 16 * (lam * (lam - 1)) ^ 2 := by
      simp only [legendreAt, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hΔ]
    exact h16.mul (hlam.pow 2)
  letI := he
  have hgeom := relative_curve_geometry R (legendreAt R lam)
  letI : SmoothOfRelativeDimension 1 (structureMap R (legendreAt R lam)) := hgeom.2.2.2.2.2.1
  letI : GeometricallyIntegral (structureMap R (legendreAt R lam)) := hgeom.2.2.2.2.2.2
  have hu : IsUnit (2 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  letI : Invertible (2 : R) := hu.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ := WeierstrassProjModel.relativeGroupLaw_exists (legendreAt R lam)
    (inferInstance : Smooth (structureMap R (legendreAt R lam))) hgeom.2.2.2.2.2.2 (legendreAt R lam).isUnit_Δ
  have hG : IsOriginLaw R (legendreAt R lam) G := ⟨hone, hcomm⟩
  obtain ⟨p, hp⟩ := StandardMarking.exists_coordinate_section (legendreAt R lam) 0 0 (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [legendreAt])
  obtain ⟨q, hq⟩ := StandardMarking.exists_coordinate_section (legendreAt R lam) 1 0 (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [legendreAt])
  obtain ⟨s, hs⟩ := StandardMarking.exists_coordinate_section (legendreAt R lam) lam 0 (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [legendreAt, WeierstrassCurve.toAffine, zero_mul, mul_zero, add_zero, zero_add,
      zero_pow (by decide : 2 ≠ 0)]
    ring)
  let P : SchemeHomOver (𝟙 (Base R)) (structureMap R (legendreAt R lam)) := ⟨p, hp.1⟩
  let Q : SchemeHomOver (𝟙 (Base R)) (structureMap R (legendreAt R lam)) := ⟨q, hq.1⟩
  let S : SchemeHomOver (𝟙 (Base R)) (structureMap R (legendreAt R lam)) := ⟨s, hs.1⟩
  obtain ⟨hP, hQ, hPQ⟩ := StandardMarking.legendre_coordinates_relations lam G hG P Q S hp hq hs
  have hdP := StandardMarking.coordinate_section_avoids (legendreAt R lam) G hG P 0 0 hp
  have hdQ := StandardMarking.coordinate_section_avoids (legendreAt R lam) G hG Q 1 0 hq
  have hdS := StandardMarking.coordinate_section_avoids (legendreAt R lam) G hG S lam 0 hs
  let M : FullLevel R (legendreAt R lam) G 2 (𝟙 (Base R)) :=
    { x := P, y := Q, killed_x := hP, killed_y := hQ
      avoids := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact False.elim (hij.elim (fun h => h rfl) (fun h => h rfl))
        · simpa only [WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,
            WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply, G.one_mul] using hdQ
        · simpa only [WeierstrassProjModel.RelativeGroupLaw.nsmul_zero,
            WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply, G.mul_one] using hdP
        · simpa only [WeierstrassProjModel.RelativeGroupLaw.nsmul_one_apply, hPQ] using hdS }
  refine ⟨he, G, hG, M, hp, hq, ?_⟩
  change HasCoordinates R (legendreAt R lam) (G.mul (𝟙 _) P Q).val lam 0
  rw [hPQ]
  exact hs
end ArithmeticThetaLegendreComparisonR0177
