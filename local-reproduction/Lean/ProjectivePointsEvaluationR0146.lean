import MarkedGroupLawDefinitionsR0146
import P2M.Sol.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain

/-! Universe-polymorphic coordinate evaluation on the specified projective cubic.
The chart dictionary and addition lemmas are reused from the controlled library;
we assemble them in universe u, with the actual prescribed identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
namespace ProjectivePointsEvaluation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization MvPolynomial
open P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain.WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F]

theorem comp_algebraMap_eq_of_fac
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    χ.comp (algebraMap R _) = algebraMap R F := by
  have h := P.2
  have e2 := kw_lrApt_coverE_f_comp_π W i
  rw [hfac, Category.assoc] at h
  erw [e2, ← Spec.map_comp] at h
  have h2 := Spec.map_injective (h.trans (by rfl : kw_lrAptb_tF (R := R) F = Spec.map (CommRingCat.ofHom (algebraMap R F))))
  have h3 := congrArg CommRingCat.Hom.hom h2
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h3
  exact h3

def algHomOfFac
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →ₐ[R] F :=
  { toRingHom := χ
    commutes' := fun r ↦ RingHom.congr_fun (comp_algebraMap_eq_of_fac W F P i χ hfac) r }

@[scoped simp] theorem algHomOfFac_toRingHom
    (P : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
    (χ : Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i : MvPolynomial (Fin 3) R)) →+* F)
    (hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i) :
    (algHomOfFac W F P i χ hfac).toRingHom = χ := rfl

theorem toAffine_eq_of_mk_eq {P Q : Fin 3 → F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) = ⟦Q⟧) :
    WeierstrassCurve.Projective.Point.toAffine (kw_lrApt_WF W F) P =
      WeierstrassCurve.Projective.Point.toAffine (kw_lrApt_WF W F) Q := by
  obtain ⟨u, rfl⟩ := Quotient.eq.mp h
  exact WeierstrassCurve.Projective.Point.toAffine_smul Q u.isUnit


theorem coordinateEvaluationExists
    {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T] (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W.toProjective))
    (hG : (G.one (𝟙 _)).1 = (kwZeroSect T W).1) :
    ∃ ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective) ≃
          (W.toProjective.baseChange F).toAffine.Point,
      IsPointsEval W.toProjective G ev ∧
      (∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F],
        ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
          by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0) ∧
      ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F]
        (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective))
        (χ : ZChartRing W.toProjective →+* F),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective →
        ∃ hxy : (W.toProjective.baseChange F).toAffine.Nonsingular (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
          ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy := by
  classical
  have hΔ : IsUnit W.Δ := WeierstrassCurve.isUnit_Δ W

  obtain ⟨u₃, toE₃, hcov₉, hcompat₃⟩ := exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain W
  obtain ⟨pcm, hpin⟩ := exists_perChart_addMorphism_of_thirdLaw_nineCoverage W u₃ toE₃ hcov₉ hcompat₃
  obtain ⟨m, hm_over, hm⟩ := exists_addMorphism_of_perChart_addMorphism_pin W pcm hpin
  have hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ (kwProjPullbackChartIsoCR T W.toProjective i j).inv ≫
        (kwProjPullbackOpenCoverCR T W.toProjective).f (i, j) ≫ m = kw_lrSixU_toE W i j l := by
    intro i j l
    have h1 := hm (i, j)
    have h2 := congrArg (fun f ↦ (kwProjPullbackChartIsoCR T W.toProjective i j).inv ≫ f) h1
    simp only [Iso.inv_hom_id_assoc] at h2
    have h3 := congrArg (fun f ↦ kw_lrSixU_locMap W i j l ≫ f) h2
    exact h3.trans (hpin i j l)

  obtain ⟨G₀, hG₀mul, hG₀one⟩ :=
    exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin W m hm_over hmpin
  have h1 : (G.one (𝟙 _)).1 = (G₀.one (𝟙 _)).1 := by rw [hG, hG₀one, Category.id_comp]
  have hGmul : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T))
      (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
      (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m := by
    intro S t x y
    rw [RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W.toProjective G G₀ h1 t x y]
    exact hG₀mul t x y

  refine ⟨fun F _ _ _ ↦ kw_lrApt_setEquiv W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro F instF instD instA P Q
    exact kw_pinpe_setEquiv_mul W hΔ m hmpin G (fun t x y ↦ hGmul t x y) F P Q
  · intro F instF instD instA σ P
    have hdec : instD = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
    subst hdec
    exact kw_lrApt_setEquiv_galNat W F (kw_pinpe_algebraMap_Δ_ne_zero W hΔ F) (K := T) σ P
  ·
    intro F instF instD instA
    have hΔF := kw_pinpe_algebraMap_Δ_ne_zero W hΔ F
    rw [kw_lrApt_setEquiv_eq_toAffine_toVec W F hΔF]
    have hfac : (⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
        by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ :
          SchemeHomOver (kw_lrAptb_tF (R := T) F) (projModelStrCR W.toProjective)).1 =
        Spec.map (CommRingCat.ofHom ((algebraMap T F).comp (kwYChartEval T W))) ≫
          (projModelAffineOpenCoverCR T W.toProjective).openCover.f (1 : Fin 3) := by
      change Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ _) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    let ψ := algHomOfFac W F _ 1 _ hfac
    have hcls := kw_lrApt_toPointClass_eq_of_fac W F _ 1 ψ hfac
    have hvec : kw_lrApt_chartEval W F 1 ψ = ![(0 : F), 1, 0] := by
      funext k
      change (algebraMap T F) (kwYChartEval T W (kw_lrChart_gen W 1 k)) = _
      rw [kwYChartEval_gen_eq]
      fin_cases k <;> simp
    rw [toAffine_eq_of_mk_eq W F (hcls.trans (by rw [hvec])), WeierstrassCurve.Projective.Point.toAffine_zero]
  ·
    intro F instF instD instA P χ hP
    have hΔF := kw_pinpe_algebraMap_Δ_ne_zero W hΔ F
    have hfac : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ (projModelAffineOpenCoverCR T W.toProjective).openCover.f (2 : Fin 3) := by
      rw [hP]; rfl
    let ψ := algHomOfFac W F P 2 χ hfac
    have hcls := kw_lrApt_toPointClass_eq_of_fac W F P 2 ψ hfac
    have hvec : kw_lrApt_chartEval W F 2 ψ = ![χ (xOverZ W.toProjective), χ (yOverZ W.toProjective), 1] := by
      funext k
      fin_cases k
      · change χ (kw_lrChart_gen W 2 0) = χ (xOverZ W.toProjective)
        rw [kw_lrApt_gen_eq_awayMk]; rfl
      · change χ (kw_lrChart_gen W 2 1) = χ (yOverZ W.toProjective)
        rw [kw_lrApt_gen_eq_awayMk]; rfl
      · exact kw_lrApt_chartEval_self W F 2 ψ
    have hns : (kw_lrApt_WF W F).Nonsingular ![χ (xOverZ W.toProjective), χ (yOverZ W.toProjective), 1] := by
      rw [← hvec]
      exact kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔF (kw_lrApt_chartEval_equation W F 2 ψ)
        (kw_lrApt_chartEval_ne_zero W F 2 ψ)
    refine ⟨(WeierstrassCurve.Projective.nonsingular_some _ _).mp hns, ?_⟩
    change kw_lrApt_setEquiv W F hΔF P = _
    rw [kw_lrApt_setEquiv_eq_toAffine_toVec W F hΔF,
      toAffine_eq_of_mk_eq W F (hcls.trans (by rw [hvec])), WeierstrassCurve.Projective.Point.toAffine_some]
    exact hns

end ProjectivePointsEvaluation

open CategoryTheory AlgebraicGeometry ArithmeticThetaCompactifiedDifferentialR0145
/-- Coordinate evaluation, including addition and Galois compatibility, in every universe. -/
theorem projective_points_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (h3 : 3 ≤ r) (he : Even r)
      (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r)),
      (G.one (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (LaurentSeries k))))).val = origin k r →
      ∃ ev : PointEvaluation k r, IsCoordinateEvaluation k r G ev := by
  intro k _ _ r h3 he G hG
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  obtain ⟨ev, hev, _, hcoord⟩ :=
    ProjectivePointsEvaluation.coordinateEvaluationExists (curve k r) G hG
  exact ⟨ev, hev, hcoord⟩

#print axioms projective_points_evaluation
end ArithmeticThetaMarkedGroupLawR0146
