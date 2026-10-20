module

public import ActualGenericGroupLawR0146
public import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
public import Theorems.Thm_WeierstrassProjModel_negMor_over

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ActualGenericGroupLaw

/-- Transporting a law also transports its inverse, on every test scheme. -/
lemma inv_transport {R : Type u} [CommRing R] {A B : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ B) (he : e.hom ≫ g = f) (G : RelativeGroupLaw R f)
    (hei : e.inv ≫ f = g) (n : B ⟶ B)
    (hn : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver t g), ((transport e.symm hei G).inv t x).val = x.val ≫ n)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (G.inv t x).val = x.val ≫ e.hom ≫ n ≫ e.inv := by
  have h := hn t (pointsEquiv e he t x)
  have hb : pointsEquiv e.symm hei t (pointsEquiv e he t x) = x := by
    apply Subtype.ext
    simp [pointsEquiv]
  change (G.inv t (pointsEquiv e.symm hei t (pointsEquiv e he t x))).val ≫ e.hom =
    (x.val ≫ e.hom) ≫ n at h
  rw [hb] at h
  have hh := congrArg (fun q => q ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh


open MonoidalCategory
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

local instance pulled_isIso {C D : Scheme.{u}} (f : D ⟶ C) {L : C.Modules}
    (j : L ⟶ (𝟙_ C.Modules)) [IsIso j] : IsIso (pulledInclusion f j) := by
  letI := unitPullback_isIso f
  unfold pulledInclusion
  infer_instance

lemma regularValue_pull {C D : Scheme.{u}} (f : D ⟶ C) {L : C.Modules}
    (j q : L ⟶ (𝟙_ C.Modules)) [IsIso j] :
    regularValue (pulledInclusion f j) (pulledInclusion f q) = f.appTop (regularValue j q) := by
  apply regularValue_from_equation
  have hq : q = dualScale (regularValue j q) j := by
    apply Scheme.Modules.hom_ext
    intro U
    ext v
    exact (regularValue_spec j q U v).trans (dualScale_app _ _ U v).symm
  calc
    pulledInclusion f q = pulledInclusion f (dualScale (regularValue j q) j) := congrArg _ hq
    _ = _ := pulled_dualScale f _ j

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaModelSymmetriesR0137 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaGeometricLiftsR0141.GeometricInversionLiftR0141
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma inversion_complement (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    (inversionMap k M rot scal iv ha) ⁻¹ᵁ (complement k M s) = complement k M s := by
  have h := inversion_power_ideal k h3 M hM s hs rot scal iv ha 1
  simp only [pow_one] at h
  have hh : (s.ker.comap (genericInclusion k M)).comap (inversionMap k M rot scal iv ha) =
      s.ker.comap (genericInclusion k M) := by
    rw [← Scheme.IdealSheafData.comap_comp, inversionMap_inclusion,
      Scheme.IdealSheafData.comap_comp, h]
  have hh' := congrArg (fun I => I.support.compl) hh
  rw [Scheme.IdealSheafData.support_comap] at hh'
  exact hh'

def complementInv (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) : complementScheme k M s ⟶ complementScheme k M s :=
  IsOpenImmersion.lift (complement k M s).ι
    ((complement k M s).ι ≫ inversionMap k M rot scal iv ha) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨_, ?_⟩, rfl⟩
      change x.val ∈ (inversionMap k M rot scal iv ha) ⁻¹ᵁ (complement k M s)
      rw [inversion_complement k h3 M hM s hs rot scal iv ha]
      exact x.property)

lemma complementInv_inclusion (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv) :
    complementInv k h3 M hM s hs rot scal iv ha ≫ (complement k M s).ι =
      (complement k M s).ι ≫ inversionMap k M rot scal iv ha :=
  IsOpenImmersion.lift_fac _ _ _


variable (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (iv : M.X ≅ M.X)
    (ha : Actions k M rot scal iv)

lemma complementInv_model :
    complementInv k h3 M hM s hs rot scal iv ha ≫ complementInclusion k M s =
      complementInclusion k M s ≫ iv.hom := by
  unfold complementInclusion
  rw [← Category.assoc, complementInv_inclusion, Category.assoc, inversionMap_inclusion,
    ← Category.assoc]

lemma complement_coordinate_parity (odd : Bool) (φ : Dual k M s (degree odd))
    (hφ : RealizesCoordinate k odd M s φ) :
    (complementInv k h3 M hM s hs rot scal iv ha).appTop
      (complementCoordinate k M s (degree odd) φ) =
      if odd then -complementCoordinate k M s (degree odd) φ
      else complementCoordinate k M s (degree odd) φ := by
  let c := complementInclusion k M s
  let f := complementInv k h3 M hM s hs rot scal iv ha
  let j := idealInclusion (s.ker ^ degree odd)
  let E := baseChangedLift c c f iv.hom
    (complementInv_model k h3 M hM s hs rot scal iv ha).symm
    (powerModule k M s (degree odd)) (modelLift k h3 M hM s hs rot scal iv ha (degree odd))
  letI : IsIso (pulledInclusion c j) := complement_power_inclusion_isIso k r M s (degree odd)
  have hj : E.hom ≫ pulledInclusion f (pulledInclusion c j) = pulledInclusion c j := by
    rw [baseChangedLift_dual, modelLift_inclusion]
  have hq : E.hom ≫ pulledInclusion f (pulledInclusion c φ) =
      pulledInclusion c (CoordinateGeometricInversionR0143.signed odd φ) := by
    rw [baseChangedLift_dual]
    congr 1
    apply Scheme.Modules.hom_ext
    intro U
    ext v
    have hp := coordinate_geometric_inversion k r hr h3 T M hM s hs odd φ hφ rot scal iv ha U v
    cases odd <;> exact hp
  have hv := regularValue_precomp E (pulledInclusion f (pulledInclusion c j))
    (pulledInclusion f (pulledInclusion c φ))
  simp only [hj, hq, regularValue_pull] at hv
  change _ = f.appTop (complementCoordinate k M s (degree odd) φ) at hv
  rw [← hv]
  cases odd
  · rfl
  · simp only [CoordinateGeometricInversionR0143.signed, ↓reduceIte, pulledInclusion, Functor.map_neg, Preadditive.neg_comp]
    rfl


/- The chart calculation follows the controlled library's homogeneous
localization construction, retained here with public, module-specific names
because the library's point-specialized chart helpers are private. -/
namespace ProjectiveNeg
open MvPolynomial HomogeneousLocalization WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra
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

lemma negGradedHom_mk_X (m : Fin 3) :
    negGradedHom (mk₃ (X m)) = mk₃ (kw_lrAddNegDiag_negSubstGen W m) := by
  show mk₃ (kw_lrAddNegDiag_negSubst W (X m)) = _
  rw [kw_lrAddNegDiag_negSubst, aeval_X]

lemma negGradedHom_fix (j : Fin 3) (hj : j = 0 ∨ j = 2) :
    negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R) := by
  rw [negGradedHom_mk_X W j]
  rcases hj with rfl | rfl <;> rfl

def negChart (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) : (𝒜 j) →+* (𝒜 j) :=
  HomogeneousLocalization.map negGradedHom (by
    rintro y ⟨n, rfl⟩
    exact Submonoid.mem_comap.mpr ⟨n, by rw [map_pow, hfix]⟩)

lemma negChart_gen (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) (m : Fin 3) :
    negChart W j hfix (gen j m)
      = kw_lrChart_dehom W j (kw_lrAddNegDiag_negSubstGen W m) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [negChart, kw_lrChart_gen, HomogeneousLocalization.map_mk,
    kw_lrChart_dehom_isHomogeneous_val W j 1 _
      (kw_lrAddNegDiag_negSubstGen_isHomogeneous W m),
    HomogeneousLocalization.val_mk]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [pow_one, negGradedHom_mk_X W m, hfix]

lemma negChart_comp_algebraMap (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) :
    (negChart W j hfix).comp (algebraMap R (𝒜 j)) = algebraMap R (𝒜 j) := by
  refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
  have halg : algebraMap R (𝒜 j) r
      = HomogeneousLocalization.mk
          ⟨0, algebraMap R (projModelGradingCR W.toProjective 0) r, 1, one_mem _⟩ := rfl
  rw [RingHom.comp_apply, halg, negChart, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  · show negGradedHom (↑(algebraMap R (projModelGradingCR W.toProjective 0) r) : ℬ) = _
    show mk₃ (kw_lrAddNegDiag_negSubst W (C r)) = mk₃ (C r)
    exact congrArg mk₃ ((kw_lrAddNegDiag_negSubst W).commutes r)
  · exact Subtype.ext (map_one _)

def negChartA (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) : (𝒜 j) →ₐ[R] (𝒜 j) :=
  { negChart W j hfix with
    commutes' := fun r =>
      RingHom.congr_fun (negChart_comp_algebraMap W j hfix) r }

lemma awayi_comp_negMor (j : Fin 3)
    (hfix : negGradedHom (mk₃ (X j : MvPolynomial (Fin 3) R))
      = mk₃ (X j : MvPolynomial (Fin 3) R)) :
    ((coverE).f j : (coverE).X j ⟶ _) ≫ negMor
      = Spec.map (CommRingCat.ofHom (negChart W j hfix)) ≫ (coverE).f j := by
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

lemma hfix2 :
    negGradedHom (mk₃ (X 2 : MvPolynomial (Fin 3) R)) = mk₃ (X 2 : MvPolynomial (Fin 3) R) :=
  negGradedHom_fix W 2 (Or.inr rfl)


lemma chart_factor :
    DrinfeldGlobal.zChartι W.toProjective ≫ kw_lrAddNegDiag_negMor W =
      Spec.map (CommRingCat.ofHom (negChart W 2 (hfix2 W))) ≫
        DrinfeldGlobal.zChartι W.toProjective := awayi_comp_negMor W 2 (hfix2 W)

lemma x_eq_gen : DrinfeldGlobal.xOverZ W.toProjective = kw_lrChart_gen W 2 0 := by
  apply HomogeneousLocalization.val_injective
  simp [DrinfeldGlobal.xOverZ, HomogeneousLocalization.Away.val_mk, kw_lrChart_gen_val,
    DrinfeldGlobal.coord]

lemma y_eq_gen : DrinfeldGlobal.yOverZ W.toProjective = kw_lrChart_gen W 2 1 := by
  apply HomogeneousLocalization.val_injective
  simp [DrinfeldGlobal.yOverZ, HomogeneousLocalization.Away.val_mk, kw_lrChart_gen_val,
    DrinfeldGlobal.coord]

lemma chart_x : negChart W 2 (hfix2 W) (DrinfeldGlobal.xOverZ W.toProjective) =
    DrinfeldGlobal.xOverZ W.toProjective := by
  rw [x_eq_gen, negChart_gen]
  simp [kw_lrAddNegDiag_negSubstGen, kw_lrChart_dehom]

lemma chart_y (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) :
    negChart W 2 (hfix2 W) (DrinfeldGlobal.yOverZ W.toProjective) =
      -DrinfeldGlobal.yOverZ W.toProjective := by
  rw [y_eq_gen, negChart_gen]
  simp only [kw_lrAddNegDiag_negSubstGen, h1, h3, map_zero, zero_mul, sub_zero,
    kw_lrChart_dehom, Matrix.cons_val_one, Matrix.cons_val_zero, map_neg, aeval_X]

end ProjectiveNeg

lemma coordinateIso_values (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha : IsCoordinateIso k M s X Y a)
    (odd : Bool) :
    a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv (cubicCoordinate k r odd)) =
      complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X) := by
  let j := pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker ^ degree odd))
  letI : IsIso j := (ha.2 odd).1
  have h := (ha.2 odd).2 ⊤ ((inv j).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))
  change complementCoordinate k M s (degree odd) _ = _ *
    (show Γ(complementScheme k M s, ⊤) from j.app ⊤ ((inv j).app ⊤ (1 : Γ(complementScheme k M s, ⊤)))) at h
  rw [inverse_inclusion_one] at h
  cases odd <;> simpa using h.symm

lemma chart_hom_ext {D : Scheme.{u}}
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) (hc : IsChartIso k r c)
    (f g : D ⟶ Spec (CommRingCat.of (ChartRing k r)))
    (hp : f ≫ chartInclusion k r ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r =
      g ≫ chartInclusion k r ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r)
    (hxy : ∀ odd : Bool, f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv
      (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
       else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)) =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k r))).inv
      (if odd then WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective
       else WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective))) : f = g := by
  apply (cancel_mono c.inv).mp
  apply cubicScheme_hom_ext k r
  · have hc' : c.inv ≫ cubicStructure k r = chartInclusion k r ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
      rw [← hc.1, c.inv_hom_id_assoc]
    simpa only [Category.assoc, hc'] using hp
  · intro odd
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      ProjectiveCubicChart.inverse_coordinates k r c hc odd] using hxy odd


lemma affine_conjugacy (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha' : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) (hc : IsChartIso k r c) :
    complementInv k h3 M hM s hs rot scal iv ha ≫ a.hom ≫ c.hom =
      a.hom ≫ c.hom ≫ Spec.map (CommRingCat.ofHom
        (ProjectiveNeg.negChart (curve k r) 2 (ProjectiveNeg.hfix2 (curve k r)))) := by
  let ν := Spec.map (CommRingCat.ofHom
    (ProjectiveNeg.negChart (curve k r) 2 (ProjectiveNeg.hfix2 (curve k r))))
  have hn : ν ≫ chartInclusion k r = chartInclusion k r ≫ kw_lrAddNegDiag_negMor (curve k r) :=
    (ProjectiveNeg.chart_factor (curve k r)).symm
  have hp : c.hom ≫ chartInclusion k r ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r = cubicStructure k r := hc.1
  apply chart_hom_ext k c hc
  · simp only [Category.assoc]
    change _ = a.hom ≫ c.hom ≫ ν ≫ chartInclusion k r ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r
    have hneg : kw_lrAddNegDiag_negMor (curve k r) ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r =
        ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := negMor_over (curve k r)
    rw [← Category.assoc ν, hn, Category.assoc, hneg]
    rw [hp, ha'.1]
    unfold complementStructure
    rw [← Category.assoc, complementInv_inclusion, Category.assoc, inversionMap_structure]
  · intro odd
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [hc.2 odd]
    rw [coordinateIso_values k M s X Y a ha' odd]
    rw [ProjectiveCubicChart.spec_map_section]
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hc0 := hc.2 false
      simp only [Bool.false_eq_true, ↓reduceIte] at hc0
      rw [ProjectiveNeg.chart_x (curve k r), hc0, coordinateIso_values k M s X Y a ha' false]
      exact complement_coordinate_parity k h3 M hM s hs rot scal iv ha false X hX
    · simp only [↓reduceIte]
      have hc1 := hc.2 true
      simp only [↓reduceIte] at hc1
      rw [ProjectiveNeg.chart_y (curve k r) rfl rfl, map_neg, map_neg, map_neg,
        hc1, coordinateIso_values k M s X Y a ha' true]
      exact complement_coordinate_parity k h3 M hM s hs rot scal iv ha true Y hY

include h3 hM in
lemma projective_conjugacy (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha' : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) (hc : IsChartIso k r c)
    (e : genericScheme k M ≅ projectiveCurve k r) (he : IsCompactificationIso k M s hs.1 a c e) :
    inversionMap k M rot scal iv ha ≫ e.hom = e.hom ≫ kw_lrAddNegDiag_negMor (curve k r) := by
  letI := generic_integral k h3 M hM
  letI := CompactifiedCoordinateIsomorphism.projective_proper k (r := r)
  letI := CompactifiedCoordinateIsomorphism.complement_dominant k h3 M hM s hs
  have hneg : kw_lrAddNegDiag_negMor (curve k r) ≫ ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r =
      ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := negMor_over (curve k r)
  refine ext_of_isDominant_of_isSeparated
    (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r) ?_ (complement k M s).ι ?_
  · rw [Category.assoc, he.1, inversionMap_structure, Category.assoc, hneg, he.1]
  · rw [← Category.assoc, ← complementInv_inclusion k h3 M hM s hs rot scal iv ha, Category.assoc, he.2.1]
    have h := congrArg (fun f => f ≫ chartInclusion k r)
      (affine_conjugacy k h3 M hM s hs rot scal iv ha X Y hX hY a ha' c hc)
    simp only [Category.assoc] at h ⊢
    have hn := ProjectiveNeg.chart_factor (curve k r)
    change chartInclusion k r ≫ kw_lrAddNegDiag_negMor (curve k r) =
      Spec.map (CommRingCat.ofHom (ProjectiveNeg.negChart (curve k r) 2
        (ProjectiveNeg.hfix2 (curve k r)))) ≫ chartInclusion k r at hn
    rw [← hn] at h
    rw [← Category.assoc (complement k M s).ι, he.2.1]
    simpa only [Category.assoc] using h

end ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison

namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ActualGenericGroupLaw ActualInverseComparison
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145

/-- The actual polygon inversion is the inverse on every test scheme. -/
theorem actual_inverse_comparison :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (G : ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G → ∀ (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (V : AlgebraicGeometry.Scheme.{u}) (t : Quiver.Hom V (AlgebraicGeometry.Spec (CommRingCat.of (LaurentSeries k)))) (x : NeronModelInfra.SchemeHomOver t (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)), (G.inv t x).val = CategoryTheory.CategoryStruct.comp x.val (ArithmeticThetaGeometricLiftsR0141.inversionMap k M rot scal inv ha) := by
  intro k _ _ r hr h3 T he M hM s hs G hG rot scal iv ha V t x
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha', _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨e, hec, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha' c hc
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  have hei : e.inv ≫ genericStructure k M =
      ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hec.1, e.inv_hom_id_assoc]
  let H := transport e.symm hei G
  have hH : ∀ {D : Scheme.{u}} (q : D ⟶ Spec (CommRingCat.of (LaurentSeries k))),
      (H.one q).val = q ≫ (kwZeroSect (LaurentSeries k) (curve k r)).val := by
    intro D q
    change (G.one q).val ≫ e.hom = _
    rw [hG.1 q]
    change (q ≫ genericPoint k M s hs.1) ≫ e.hom = _
    rw [Category.assoc, hec.2.2]
    rfl
  have hi := inv_transport e hec.1 G hei (kw_lrAddNegDiag_negMor (curve k r))
    (fun q y => RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
      (curve k r) H hH q y) t x
  have hn := projective_conjugacy k h3 M hM s hs rot scal iv ha X Y hX hY a ha' c hc e hec
  rw [hi, ← Category.assoc e.hom, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

#print axioms actual_inverse_comparison
end ArithmeticThetaMarkedGroupLawR0146
