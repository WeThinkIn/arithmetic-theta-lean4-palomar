module

public import TwoTorsionAffineCoordinatesR0177
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
public import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota

@[expose] public section

/-! Arbitrary affine two-torsion coordinates. The chart reflection calculation
is adapted from the library proof of `negMor_chartFactor`; here its target ring
is arbitrary. The domain-base inverse theorem is used only over the universal
smooth coefficient ring, with the original arbitrary ring as the test algebra. -/
namespace ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open MvPolynomial HomogeneousLocalization WeierstrassCurve WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W
set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W
set_option quotPrecheck false in
local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W
set_option quotPrecheck false in
local notation "negMor" => kw_lrAddNegDiag_negMor W

private theorem sol_negGradedHom_mk_X (m : Fin 3) :
    negGradedHom (mk₃ (X m)) = mk₃ (kw_lrAddNegDiag_negSubstGen W m) := by
  show mk₃ (kw_lrAddNegDiag_negSubst W (X m)) = _
  rw [kw_lrAddNegDiag_negSubst, aeval_X]

private theorem sol_negGradedHom_fix (j : Fin 3) (hj : j = 0 ∨ j = 2) :
    negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R) := by
  rw [sol_negGradedHom_mk_X W j]
  rcases hj with rfl | rfl <;> rfl

private def sol_negChart (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) : (𝒜 j) →+* (𝒜 j) :=
  HomogeneousLocalization.map negGradedHom (by
    rintro y ⟨n, rfl⟩
    exact Submonoid.mem_comap.mpr ⟨n, by rw [map_pow, hfix]⟩)

private theorem sol_negChart_gen (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) (m : Fin 3) :
    sol_negChart W j hfix (gen j m)
      = kw_lrChart_dehom W j (kw_lrAddNegDiag_negSubstGen W m) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [sol_negChart, kw_lrChart_gen, HomogeneousLocalization.map_mk,
    kw_lrChart_dehom_isHomogeneous_val W j 1 _
      (kw_lrAddNegDiag_negSubstGen_isHomogeneous W m),
    HomogeneousLocalization.val_mk]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [pow_one, sol_negGradedHom_mk_X W m, hfix]

private theorem sol_negChart_comp_algebraMap (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) :
    (sol_negChart W j hfix).comp (algebraMap R (𝒜 j)) = algebraMap R (𝒜 j) := by
  refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
  have halg : algebraMap R (𝒜 j) r
      = HomogeneousLocalization.mk
          ⟨0, algebraMap R (projModelGradingCR W.toProjective 0) r, 1, one_mem _⟩ := rfl
  rw [RingHom.comp_apply, halg, sol_negChart, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  · show negGradedHom (↑(algebraMap R (projModelGradingCR W.toProjective 0) r) : ℬ) = _
    show mk₃ (kw_lrAddNegDiag_negSubst W (C r)) = mk₃ (C r)
    exact congrArg mk₃ ((kw_lrAddNegDiag_negSubst W).commutes r)
  · exact Subtype.ext (map_one _)

private def sol_negChartA (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) : (𝒜 j) →ₐ[R] (𝒜 j) :=
  { sol_negChart W j hfix with
    commutes' := fun r =>
      RingHom.congr_fun (sol_negChart_comp_algebraMap W j hfix) r }

private theorem sol_awayi_comp_negMor (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) :
    ((coverE).f j : (coverE).X j ⟶ _) ≫ negMor
      = Spec.map (CommRingCat.ofHom (sol_negChart W j hfix)) ≫ (coverE).f j := by
  have key : ∀ (t : ℬ) (ht : t ∈ projModelGradingCR W.toProjective 1)
      (hst : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R)) = t)
      (hpow : Submonoid.powers (mk₃ (X j : MvPolynomial (Fin 3) R))
        ≤ (Submonoid.powers t).comap negGradedHom),
      Proj.awayι (projModelGradingCR W.toProjective) t ht one_pos ≫ negMor
      = Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map negGradedHom hpow
            : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (mk₃ (X j : MvPolynomial (Fin 3) R))
              →+* HomogeneousLocalization.Away (projModelGradingCR W.toProjective) t))
        ≫ Proj.awayι (projModelGradingCR W.toProjective) _
            (kw_lrChart_mkX_mem_one W j) one_pos := by
    intro t ht hst hpow
    subst hst
    exact Proj.awayι_comp_map negGradedHom
      (kw_lrAddNegDiag_negGradedHom_irrelevant_le W) one_pos
      (mk₃ (X j : MvPolynomial (Fin 3) R)) (kw_lrChart_mkX_mem_one W j)
  exact key _ (kw_lrChart_mkX_mem_one W j) hfix (by
    rintro y ⟨n, rfl⟩; exact Submonoid.mem_comap.mpr ⟨n, by rw [map_pow, hfix]⟩)

private theorem sol_hfix2 :
    negGradedHom (mk₃ (X 2 : MvPolynomial (Fin 3) R)) = mk₃ (X 2 : MvPolynomial (Fin 3) R) :=
  sol_negGradedHom_fix W 2 (Or.inr rfl)


open WeierstrassCurve.DrinfeldGlobal
open P2MW.S_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain.WeierstrassProjModel
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A fixed point of the actual projective reflection satisfies its exact ordinate equation. -/
lemma ordinate_of_fixed {S : Type u} [CommRing S]
    (ψ : ZChartRing W.toProjective →+* S)
    (hfixed : (Spec.map (CommRingCat.ofHom ψ) ≫ zChartι W.toProjective) ≫
      kw_lrAddNegDiag_negMor W = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι W.toProjective) :
    ψ (yOverZ W.toProjective) = -ψ (yOverZ W.toProjective) -
      ψ (algebraMap R _ W.a₁) * ψ (xOverZ W.toProjective) - ψ (algebraMap R _ W.a₃) := by
  have hn := sol_awayi_comp_negMor W 2 (sol_hfix2 W)
  change zChartι W.toProjective ≫ _ = _ ≫ zChartι W.toProjective at hn
  rw [Category.assoc, hn, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp] at hfixed
  have heq := Spec.map_injective ((cancel_mono (zChartι W.toProjective)).mp hfixed)
  have hy := RingHom.congr_fun (congrArg CommRingCat.Hom.hom heq) (yOverZ W.toProjective)
  have hxgen : gen 2 0 = xOverZ W.toProjective := by rw [kw_lrApt_gen_eq_awayMk]; rfl
  have hygen : gen 2 1 = yOverZ W.toProjective := by rw [kw_lrApt_gen_eq_awayMk]; rfl
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, ← hygen] at hy
  change ψ (sol_negChart W 2 (sol_hfix2 W) (gen 2 1)) = ψ (gen 2 1) at hy
  rw [sol_negChart_gen] at hy
  change ψ ((kw_lrChart_dehom W 2) (-X 1 - C W.a₁ * X 0 - C W.a₃ * X 2)) = ψ (gen 2 1) at hy
  simp only [map_sub, map_neg, map_mul, kw_lrChart_dehom, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, hxgen, hygen, kw_lrApt_gen_self, map_one, mul_one] at hy
  exact hy.symm

lemma exists_origin_law [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    ∃ G : RelativeGroupLaw R (projModelStrCR W.toProjective),
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G.one t).val = t ≫ (kwZeroSect R W).val := by
  obtain ⟨u₃, toE₃, hcov₉, hcompat₃⟩ := exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain W
  obtain ⟨pcm, hpin⟩ := exists_perChart_addMorphism_of_thirdLaw_nineCoverage W u₃ toE₃ hcov₉ hcompat₃
  obtain ⟨m, hm_over, hm⟩ := exists_addMorphism_of_perChart_addMorphism_pin W pcm hpin
  have hmpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ (kwProjPullbackChartIsoCR R W.toProjective i j).inv ≫
        (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m = kw_lrSixU_toE W i j l := by
    intro i j l
    have h2 := congrArg (fun f ↦ (kwProjPullbackChartIsoCR R W.toProjective i j).inv ≫ f) (hm (i,j))
    simp only [Iso.inv_hom_id_assoc] at h2
    exact (congrArg (kw_lrSixU_locMap W i j l ≫ ·) h2).trans (hpin i j l)
  obtain ⟨G, _, hone⟩ := exists_relativeGroupLaw_mul_eq_one_eq_zeroSect_of_addMorphism_sixU_pin W m hm_over hmpin
  exact ⟨G, hone⟩

lemma chart_scalars {S : Type u} [CommRing S] (f : R →+* S)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR W.toProjective))
    (ψ : ZChartRing W.toProjective →+* S)
    (hfac : P.val = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι W.toProjective) :
    ψ.comp (algebraMap R _) = f := by
  have h := P.property
  have e2 := kw_lrApt_coverE_f_comp_π W 2
  rw [hfac, Category.assoc] at h
  erw [e2, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The coefficient base is a domain, but the point may take values in any ring. -/
lemma ordinate_of_killed_domain [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (hG : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      (G.one t).val = t ≫ (kwZeroSect R W).val)
    {S : Type u} [CommRing S] (f : R →+* S)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR W.toProjective))
    (hP : G.mul _ P P = G.one _)
    (ψ : ZChartRing W.toProjective →+* S)
    (hfac : P.val = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι W.toProjective) :
    ψ (yOverZ W.toProjective) = -ψ (yOverZ W.toProjective) -
      f W.a₁ * ψ (xOverZ W.toProjective) - f W.a₃ := by
  letI := G.pointGroup (Spec.map (CommRingCat.ofHom f))
  have hi : G.inv _ P = P := inv_eq_of_mul_eq_one_left hP
  have hneg := RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect W G hG _ P
  rw [hi, hfac] at hneg
  have h := ordinate_of_fixed W ψ hneg.symm
  have hc := chart_scalars W f P ψ hfac
  simpa only [show ψ (algebraMap R _ W.a₁) = f W.a₁ from RingHom.congr_fun hc W.a₁,
    show ψ (algebraMap R _ W.a₃) = f W.a₃ from RingHom.congr_fun hc W.a₃] using h

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
local instance : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm

abbrev UniversalRing : Type u := MvPolynomial (Fin 5) (ULift.{u} ℤ)
abbrev UniversalCurve : WeierstrassCurve UniversalRing := ⟨X 0, X 1, X 2, X 3, X 4⟩

lemma universal_discriminant_ne_zero : UniversalCurve.{u}.Δ ≠ 0 := by
  intro h
  let ev : UniversalRing.{u} →+* ULift.{u} ℤ := MvPolynomial.eval ![0, 0, 0, -1, 0]
  have hm := congrArg ev h
  norm_num [ev, UniversalCurve, Matrix.cons_val, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hm
  have h64 : (64 : ℤ) = 0 := congrArg ULift.down hm
  omega

abbrev SmoothUniversalRing : Type u := Localization.Away UniversalCurve.{u}.Δ
abbrev SmoothUniversalCurve : WeierstrassCurve SmoothUniversalRing :=
  UniversalCurve.{u}.map (algebraMap UniversalRing.{u} SmoothUniversalRing.{u})

instance : IsDomain SmoothUniversalRing.{u} :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors universal_discriminant_ne_zero.{u})
instance : IsNoetherianRing SmoothUniversalRing.{u} :=
  IsLocalization.isNoetherianRing (Submonoid.powers UniversalCurve.{u}.Δ) _ inferInstance
instance : SmoothUniversalCurve.{u}.IsElliptic := ⟨by
  rw [WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit UniversalCurve.{u}.Δ⟩

/-- The coefficient map is the evaluation determined by the five given coefficients. -/
lemma exists_universal_map [W.IsElliptic] :
    ∃ c : SmoothUniversalRing.{u} →+* R, SmoothUniversalCurve.{u}.map c = W := by
  let f : UniversalRing.{u} →+* R := MvPolynomial.eval₂Hom
    ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hf : UniversalCurve.{u}.map f = W := by ext <;> simp [UniversalCurve, f, WeierstrassCurve.map, Matrix.cons_val]
  have hu : IsUnit (f UniversalCurve.{u}.Δ) := by
    rw [← WeierstrassCurve.map_Δ, hf]
    exact WeierstrassCurve.isUnit_Δ W
  refine ⟨IsLocalization.Away.lift UniversalCurve.{u}.Δ hu, ?_⟩
  rw [SmoothUniversalCurve, WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hf]

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177

/-- Pull back the universal law, compare it with the prescribed law, and transport coordinates. -/
lemma ordinate_of_killed [Algebra ℚ R] [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hP : G.nsmul (𝟙 (Base R)) 2 P = G.one (𝟙 (Base R)))
    (χ : ChartRing R W →+* R)
    (hχ : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W) :
    χ (yOverZ W.toProjective) =
      -(algebraMap ℚ R (1/2)) * (W.a₁ * χ (xOverZ W.toProjective) + W.a₃) := by
  obtain ⟨c, hc⟩ := exists_universal_map W
  subst W
  let U := SmoothUniversalCurve.{u}
  obtain ⟨H, hH⟩ := exists_origin_law U
  obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom U.toProjective c
  have hcart := isPullback_projMap_of_isCoefficientHom U.toProjective c φ hφ hcoef
  obtain ⟨G', hmul, hone⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback c
    (projModelStrCR U.toProjective) (projModelStrCR (U.toProjective.map c))
    (Proj.map φ hφ) hcart H
  have hone' := fun {S : Scheme.{u}} (s : S ⟶ Base R) =>
    one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback U.toProjective c φ hφ hcoef hcart
      H G' (fun t => hH t) (fun t => hone t) s
  have he : (G.one (𝟙 (Base R))).val = (G'.one (𝟙 (Base R))).val := by
    rw [hG.1, hone']
    rfl
  have hd : G'.mul (𝟙 (Base R)) P P = G'.one (𝟙 (Base R)) := by
    rw [← RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (U.toProjective.map c) G G' he]
    have hPP : G.mul (𝟙 (Base R)) P P = G.one (𝟙 (Base R)) := by
      simpa only [show 2 = 1 + 1 from rfl, G.nsmul_succ, G.nsmul_one_apply,
        G.nsmul_zero, G.one_mul] using hP
    exact hPP.trans (Subtype.ext he)
  have hbase : P.val ≫ projModelStrCR (U.toProjective.map c) = 𝟙 (Base R) := P.property
  let Q : SchemeHomOver (Spec.map (CommRingCat.ofHom c)) (projModelStrCR U.toProjective) :=
    ⟨P.val ≫ Proj.map φ hφ, by rw [Category.assoc, hcart.w, ← Category.assoc, hbase, Category.id_comp]⟩
  have hQ : H.mul _ Q Q = H.one _ := by
    -- Package the dependent point before rewriting the identity composite base map.
    have hex : ∃ Q' : SchemeHomOver ((𝟙 (Base R)) ≫ Spec.map (CommRingCat.ofHom c))
        (projModelStrCR U.toProjective),
        Q'.val = P.val ≫ Proj.map φ hφ ∧ H.mul _ Q' Q' = H.one _ := by
      refine ⟨⟨P.val ≫ Proj.map φ hφ, ?_⟩, rfl, ?_⟩
      · rw [Category.assoc, hcart.w, ← Category.assoc, hbase]
      · apply Subtype.ext
        have h := hmul (𝟙 (Base R)) P P
        rw [hd, hone] at h
        exact h.symm
    rw [Category.id_comp] at hex
    obtain ⟨Q', hv, hk⟩ := hex
    have heq : Q' = Q := Subtype.ext hv
    simpa only [heq] using hk
  obtain ⟨θ, hθ, hxθ, hyθ⟩ := exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
    U.toProjective c φ hφ hcoef
  have hfac : Q.val = Spec.map (CommRingCat.ofHom (χ.comp θ)) ≫ zChartι U.toProjective := by
    change P.val ≫ Proj.map φ hφ = _
    rw [hχ, Category.assoc]
    change Spec.map (CommRingCat.ofHom χ) ≫ (zChartι (U.toProjective.map c) ≫ Proj.map φ hφ) = _
    rw [hθ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hy := ordinate_of_killed_domain U H (fun t => hH t) c Q hQ (χ.comp θ) hfac
  simp only [RingHom.comp_apply] at hy
  rw [hyθ, hxθ] at hy
  have hhalf : algebraMap ℚ R (1/2) * 2 = 1 := by
    have h := congrArg (algebraMap ℚ R) (show (1/2 : ℚ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  change χ (yOverZ (U.toProjective.map c)) =
    -(algebraMap ℚ R (1/2)) * (c U.a₁ * χ (xOverZ (U.toProjective.map c)) + c U.a₃)
  linear_combination (algebraMap ℚ R (1/2)) * hy -
    (χ (yOverZ (U.toProjective.map c))) * hhalf

lemma coordinates_of_killed_avoids [Algebra ℚ R] [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
    (hP : G.nsmul (𝟙 (Base R)) 2 P = G.one (𝟙 (Base R)))
    (havoid : Disjoint (Set.range P.val) (Set.range (origin R W))) :
    ∃ x : R, HasCoordinates R W P.val x
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * x + W.a₃)) := by
  obtain ⟨χ, hχ⟩ := TwoTorsionAffineCoordinates.exists_chart_factorization W P.val havoid
  exact ⟨χ (xOverZ W.toProjective), P.property, χ, hχ, rfl,
    ordinate_of_killed W G hG P hP χ hχ⟩

end
end ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates

namespace ArithmeticThetaArbitraryAffineR0202
open AlgebraicGeometry CategoryTheory NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArbitraryTwoCoordinates
universe u
/-- The three nonidentity full two-torsion labels have the prescribed global affine coordinates. -/
theorem arbitrary_two_coordinates :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (G : Law R W) (hG : IsOriginLaw R W G)
      (M : FullLevel R W G 2 (CategoryTheory.CategoryStruct.id (Base R))),
      ∃ e : Fin 3 → R, TwoCoordinates R W G M e := by
  intro R _ _ W _ G hG M
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


#print axioms arbitrary_two_coordinates
end ArithmeticThetaArbitraryAffineR0202
