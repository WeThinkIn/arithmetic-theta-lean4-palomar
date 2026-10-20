module

public import LegendreComparisonDefinitionsR0177
public import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel

@[expose] public section

/-! Global affine coordinates of the three nonidentity two-torsion sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
namespace TwoTorsionAffineCoordinates
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
attribute [local instance] MvPolynomial.gradedAlgebra

/- The complement calculation is made universe-polymorphic here. It uses
   Z=0 => X³=0 in the homogeneous cubic and the origin-chart kernel. -/
section Cover

open MvPolynomial TopologicalSpace

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection


lemma exists_chart_factorization {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (P : Base R ⟶ Curve R W)
    (hP : Disjoint (Set.range P) (Set.range (origin R W))) :
    ∃ χ : ChartRing R W →+* R,
      P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W := by
  have hrange : Set.range P ⊆ Set.range (zChartι W.toProjective) := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    by_contra h
    exact Set.disjoint_left.mp hP ⟨z, rfl⟩
      ((not_mem_basicOpen_iff_mem_range_kwZeroSect W (P z)).mp h)
  let g := IsOpenImmersion.lift (zChartι W.toProjective) P hrange
  refine ⟨(Spec.preimage g).hom, ?_⟩
  change P = Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) ≫ zChartι W.toProjective
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact (IsOpenImmersion.lift_fac _ _ hrange).symm

lemma ordinate_of_killed {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hP : G.nsmul (𝟙 (Base R)) 2 P = G.one (𝟙 (Base R)))
    (χ : ChartRing R W →+* R)
    (hχ : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W) :
    χ (yOverZ W.toProjective) =
      -(algebraMap ℚ R (1/2)) * (W.a₁ * χ (xOverZ W.toProjective) + W.a₃) := by
  classical
  let F := FractionRing R
  let f : R →+* F := algebraMap R F
  let t : Spec (CommRingCat.of F) ⟶ Base R := Spec.map (CommRingCat.ofHom f)
  let Q := schemeHomOverComp t (Category.comp_id t) P
  have hQ : G.nsmul t 2 Q = G.one t := by
    rw [← G.nsmul_natural (𝟙 _) t t (Category.comp_id t), hP,
      G.one_natural]
  have hQfac : Q.val = Spec.map (CommRingCat.ofHom (f.comp χ)) ≫ zChartι W.toProjective := by
    change t ≫ P.val = _
    rw [hχ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  obtain ⟨ev, hev, _, hcoord⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by simpa [origin] using hG.1 (𝟙 (Base R)))
  have hz : ev F (G.one t) = 0 := by
    have h := hev.1 F (G.one t) (G.one t)
    rw [G.one_mul] at h
    exact (add_left_cancel ((add_zero _).trans h)).symm
  have hdouble : ev F Q + ev F Q = 0 := by
    have hQQ : G.mul t Q Q = G.one t := by
      simpa only [show 2 = 1 + 1 from rfl, G.nsmul_succ, G.nsmul_one_apply,
        G.nsmul_zero, G.one_mul] using hQ
    rw [← hev.1 F Q Q, hQQ, hz]
  obtain ⟨hxy, heq⟩ := hcoord F Q (f.comp χ) hQfac
  have hneg : ev F Q = -(ev F Q) := eq_neg_of_add_eq_zero_left hdouble
  rw [heq, WeierstrassCurve.Affine.Point.neg_some] at hneg
  have hy := (WeierstrassCurve.Affine.Point.some.inj hneg).2
  have hyR : χ (yOverZ W.toProjective) =
      -χ (yOverZ W.toProjective) - W.a₁ * χ (xOverZ W.toProjective) - W.a₃ := by
    apply (IsFractionRing.injective R F)
    change f (χ (yOverZ W.toProjective)) =
      -f (χ (yOverZ W.toProjective)) - f W.a₁ * f (χ (xOverZ W.toProjective)) - f W.a₃ at hy
    simpa only [map_sub, map_neg, map_mul] using hy
  have hhalf : algebraMap ℚ R (1/2) * 2 = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (1/2 : ℚ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination (algebraMap ℚ R (1/2)) * hyR -
    (χ (yOverZ W.toProjective)) * hhalf

lemma coordinates_of_killed_avoids {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hP : G.nsmul (𝟙 (Base R)) 2 P = G.one (𝟙 (Base R)))
    (havoid : Disjoint (Set.range P.val) (Set.range (origin R W))) :
    ∃ x : R, HasCoordinates R W P.val x
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * x + W.a₃)) := by
  obtain ⟨χ, hχ⟩ := exists_chart_factorization W P.val havoid
  exact ⟨χ (xOverZ W.toProjective), P.property, χ, hχ, rfl,
    ordinate_of_killed W G hG P hP χ hχ⟩

end TwoTorsionAffineCoordinates

open AlgebraicGeometry CategoryTheory NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 TwoTorsionAffineCoordinates

/-- Each nonzero two-torsion label has global affine coordinates, with its
    ordinate determined by the completed square. -/
theorem two_torsion_affine_coordinates :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : Law R W) (hG : IsOriginLaw R W G)
      (M : FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (Base R))),
      ∃ e : Fin 3 → R, TwoCoordinates R W G M e := by
  intro R _ _ _ _ _ W _ G hG M
  have hax : Disjoint (Set.range M.x.val) (Set.range (origin R W)) := by
    simpa only [Fin.val_one, Fin.val_zero, G.nsmul_one_apply, G.nsmul_zero,
      G.mul_one] using M.avoids 1 0 (Or.inl (by decide))
  have hay : Disjoint (Set.range M.y.val) (Set.range (origin R W)) := by
    simpa only [Fin.val_one, Fin.val_zero, G.nsmul_one_apply, G.nsmul_zero,
      G.one_mul] using M.avoids 0 1 (Or.inr (by decide))
  have haz : Disjoint (Set.range (G.mul (𝟙 (Base R)) M.x M.y).val)
      (Set.range (origin R W)) := by
    simpa only [Fin.val_one, G.nsmul_one_apply] using
      M.avoids 1 1 (Or.inl (by decide))
  have hkz : G.nsmul (𝟙 (Base R)) 2 (G.mul (𝟙 (Base R)) M.x M.y) =
      G.one (𝟙 (Base R)) := by
    letI : CommGroup (SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :=
      { G.pointGroup (𝟙 (Base R)) with mul_comm := hG.2 (𝟙 (Base R)) }
    have hx : M.x ^ 2 = 1 :=
      (FullLevelTorsionSplittingR0175.nsmul_pow G _ 2 M.x).symm.trans M.killed_x
    have hy : M.y ^ 2 = 1 :=
      (FullLevelTorsionSplittingR0175.nsmul_pow G _ 2 M.y).symm.trans M.killed_y
    rw [FullLevelTorsionSplittingR0175.nsmul_pow G]
    change (M.x * M.y) ^ 2 = 1
    rw [mul_pow, hx, hy, one_mul]
  obtain ⟨x, hx⟩ := coordinates_of_killed_avoids W G hG M.x M.killed_x hax
  obtain ⟨y, hy⟩ := coordinates_of_killed_avoids W G hG M.y M.killed_y hay
  obtain ⟨z, hz⟩ := coordinates_of_killed_avoids W G hG
    (G.mul (𝟙 (Base R)) M.x M.y) hkz haz
  refine ⟨![x, y, z], ?_⟩
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

#print axioms two_torsion_affine_coordinates
end ArithmeticThetaLegendreComparisonR0177
