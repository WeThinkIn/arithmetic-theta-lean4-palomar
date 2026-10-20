module

public import LegendreComparisonDefinitionsR0177
public import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
namespace OrderedLegendreParameterRigidity
open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts

instance chart_open {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    IsOpenImmersion (chartInclusion R W) :=
  inferInstanceAs (IsOpenImmersion (zChartι W.toProjective))

abbrev scalar {R : Type u} [CommRing R] (W : WeierstrassCurve R) :=
  VariableChange.WMLocal.cZ W

lemma chart_structure {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    chartInclusion R W ≫ structureMap R W = Spec.map (CommRingCat.ofHom (scalar W)) :=
  ChartEquiv.WMLocal.zChartι_comp_projModelStrCR W

lemma evaluation_scalar {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (χ : ChartRing R W →+* R)
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W) ≫ structureMap R W = 𝟙 _) :
    ∀ a, χ (scalar W a) = a := by
  rw [Category.assoc, chart_structure, ← Spec.map_comp] at h
  have hh : CommRingCat.ofHom (scalar W) ≫ CommRingCat.ofHom χ = 𝟙 _ :=
    Spec.map_injective (h.trans (Spec.map_id _).symm)
  exact fun a => CategoryTheory.congr_fun hh a

lemma evaluation_comp {R : Type u} [CommRing R] (W V : WeierstrassCurve R)
    (f : Curve R W ⟶ Curve R V) (e : ChartRing R V →+* ChartRing R W)
    (he : Spec.map (CommRingCat.ofHom e) ≫ chartInclusion R V = chartInclusion R W ≫ f)
    (χ : ChartRing R W →+* R) (ψ : ChartRing R V →+* R)
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ chartInclusion R V) : χ.comp e = ψ := by
  change (CommRingCat.ofHom (χ.comp e)).hom = (CommRingCat.ofHom ψ).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  let : Mono (chartInclusion R V) := inferInstanceAs (Mono (zChartι V.toProjective))
  apply (cancel_mono (chartInclusion R V)).mp
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, he, ← Category.assoc]
  exact h

/-- Over a local base the polar filtration makes a pointed isomorphism triangular.
The two ordered affine sections then determine every translation coefficient. -/
lemma local_a4 {R : Type u} [CommRing R] [IsLocalRing R]
    (W V : WeierstrassCurve R)
    (p0 p1 : Base R ⟶ Curve R W)
    (q0 q1 : Base R ⟶ Curve R V)
    (hp0 : HasCoordinates R W p0 0 0)
    (hp1 : HasCoordinates R W p1 1 0)
    (hq0 : HasCoordinates R V q0 0 0)
    (hq1 : HasCoordinates R V q1 1 0)
    (f : Curve R W ≅ Curve R V)
    (hf : f.hom ≫ structureMap R V = structureMap R W)
    (ho : origin R W ≫ f.hom = origin R V)
    (h0 : p0 ≫ f.hom = q0) (h1 : p1 ≫ f.hom = q1) : W.a₄ = V.a₄ := by
  obtain ⟨e, hec, hei⟩ := ChartEquiv.solution R W V f hf ho
  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := exists_ringHom_originChartRing_powerSeries W
  obtain ⟨l, hlc, hlx, hly, hF2, hF3⟩ := LaurentFiltration.solution R W Φ hΦc hΦx hΦz
  obtain ⟨hx1, hx2, hy1, hy2⟩ := LaurentCoeff.solution R W V f hf ho
    e.toRingHom hei Φ hΦc hΦx hΦz l hlc hlx hly
  obtain ⟨a, b, r, s, t, hx, hy⟩ := VariableChange.WMLocal.triangular_of_coeff
    (scalar W) (xOverZ W.toProjective) (yOverZ W.toProjective)
    (xOverZ V.toProjective) (yOverZ V.toProjective) e.toRingHom l
    hF2 hF3 hx1 hx2 hy1 hy2
  obtain ⟨hp0o, χ0, rfl, χ0x, χ0y⟩ := hp0
  obtain ⟨hp1o, χ1, rfl, χ1x, χ1y⟩ := hp1
  obtain ⟨hq0o, ψ0, rfl, ψ0x, ψ0y⟩ := hq0
  obtain ⟨hq1o, ψ1, rfl, ψ1x, ψ1y⟩ := hq1
  have hc0 := evaluation_scalar W χ0 hp0o
  have hc1 := evaluation_scalar W χ1 hp1o
  have hχ0 := evaluation_comp W V f.hom e.toRingHom hei χ0 ψ0 h0
  have hχ1 := evaluation_comp W V f.hom e.toRingHom hei χ1 ψ1 h1
  have ev0 (z : ChartRing R V) : χ0 (e z) = ψ0 z := RingHom.congr_fun hχ0 z
  have ev1 (z : ChartRing R V) : χ1 (e z) = ψ1 z := RingHom.congr_fun hχ1 z
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx hy
  have hr : r = 0 := by
    have h := congrArg χ0 hx
    simpa only [ev0, ψ0x, map_add, map_mul, hc0, χ0x, mul_zero, zero_add] using h.symm
  have ha : (a : R) = 1 := by
    have h := congrArg χ1 hx
    simpa only [ev1, ψ1x, map_add, map_mul, hc1, χ1x, mul_one, hr, add_zero] using h.symm
  have ht : t = 0 := by
    have h := congrArg χ0 hy
    simpa only [ev0, ψ0y, map_add, map_mul, hc0, χ0x, χ0y, mul_zero, zero_add] using h.symm
  have hs : s = 0 := by
    have h := congrArg χ1 hy
    simpa only [ev1, ψ1y, map_add, map_mul, hc1, χ1x, χ1y, mul_zero, mul_one,
      zero_add, ht, add_zero] using h.symm
  have ha' : a = 1 := Units.ext ha
  subst a
  obtain ⟨g, gx, gy⟩ := VariableChange.WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv
    W V e hec 1 b r s t hx hy
  simp only [hr, hs, ht, inv_one, Units.val_one, one_smul, mul_zero, neg_zero,
    sub_self, map_zero, add_zero] at gx gy
  obtain ⟨C, hC, hu, hCr, hCs, hCt⟩ := Triangular.solution R W V g 1 b⁻¹ 0 0 0
    (by simpa using gx) (by simpa using gy)
  have hCs' : C.s = 0 := by simpa only [hu.1, Units.val_one, one_mul] using hCs
  have hi : (↑C.u⁻¹ : R)^2 = 1 := by
    have hh : (↑C.u⁻¹ : R)^2 * (↑C.u : R)^2 = 1 := by rw [← mul_pow, Units.inv_mul, one_pow]
    simpa only [hu.1, Units.val_one, mul_one] using hh
  have h4 : (↑C.u⁻¹ : R)^4 = 1 := by rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, hi, one_pow]
  have h := congrArg WeierstrassCurve.a₄ hC
  simpa [WeierstrassCurve.variableChange_a₄, hCr, hCs', hCt, h4] using h

section CoefficientChange
open HomogeneousLocalization
variable {R S : Type u} [CommRing R] [CommRing S]
variable (W : WeierstrassCurve R) (σ : R →+* S)
variable (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map σ).toProjective)
variable (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map σ).toProjective) ≤
  (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
variable (hcoef : IsCoefficientHom W.toProjective σ φ)

private lemma chart_comp_aux :
    ∀ (s' : ProjModelRingCR (W.map σ).toProjective)
      (_e : φ (coord W.toProjective 2) = s')
      (hs' : s' ∈ projModelGradingCR (W.map σ).toProjective 1)
      (hle : Submonoid.powers (coord W.toProjective 2) ≤ (Submonoid.powers s').comap φ),
      Proj.awayι (projModelGradingCR (W.map σ).toProjective) s' hs' one_pos ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map φ hle)) ≫ chartInclusion R W := by
  rintro s' rfl hs' hle
  exact Proj.awayι_comp_map φ hφ one_pos _ (coord_mem W.toProjective 2)

include hcoef

lemma coefficient_chart :
    ∃ a : ChartRing R W →+* ChartRing S (W.map σ),
      chartInclusion S (W.map σ) ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom a) ≫ chartInclusion R W ∧
      a (xOverZ W.toProjective) = xOverZ (W.map σ).toProjective ∧
      a (yOverZ W.toProjective) = yOverZ (W.map σ).toProjective := by
  have e : φ (coord W.toProjective 2) = coord (W.map σ).toProjective 2 := hcoef.2 2
  have hle : Submonoid.powers (coord W.toProjective 2) ≤
      (Submonoid.powers (coord (W.map σ).toProjective 2)).comap φ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp [e]⟩
  let a : ChartRing R W →+* ChartRing S (W.map σ) := HomogeneousLocalization.map φ hle
  refine ⟨a, chart_comp_aux W σ φ hφ _ e (coord_mem _ 2) hle, ?_, ?_⟩
  · apply HomogeneousLocalization.val_injective
    simp only [a, xOverZ, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
      HomogeneousLocalization.val_mk]
    congr 1
    · exact hcoef.2 0
    · exact Subtype.ext (by simp [e])
  · apply HomogeneousLocalization.val_injective
    simp only [a, yOverZ, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
      HomogeneousLocalization.val_mk]
    congr 1
    · exact hcoef.2 1
    · exact Subtype.ext (by simp [e])

lemma coefficient_origin :
    origin S (W.map σ) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom σ) ≫ origin R W := by
  obtain ⟨hW, hxW, hzW⟩ := isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  obtain ⟨hS, hxS, hzS⟩ := isOriginChartSection_kwZeroSect_kwYChartEval (W.map σ).toProjective
  obtain ⟨χ, hχ, hc, hx, hz⟩ :=
    exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom W.toProjective σ φ hφ hcoef
      (kwYChartEval S (W.map σ))
  have he : χ = σ.comp (kwYChartEval R W) := by
    apply ringHom_originChartRing_ext W
    · intro t
      rw [hc, RingHom.comp_apply]
      have h1 := RingHom.congr_fun (kwYChartEval_section R W) t
      have h2 := RingHom.congr_fun (kwYChartEval_section S (W.map σ)) (σ t)
      simpa only [RingHom.comp_apply, RingHom.id_apply] using h2.trans (congrArg σ h1).symm
    · simpa only [RingHom.comp_apply, hxW, hxS, map_zero] using hx
    · simpa only [RingHom.comp_apply, hzW, hzS, map_zero] using hz
  change (kwZeroSect S (W.map σ)).val ≫ _ = _ ≫ (kwZeroSect R W).val
  rw [hW, hS, Category.assoc, hχ, he, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

lemma coefficient_coordinates (P : Base R ⟶ Curve R W) (x y : R)
    (hp : HasCoordinates R W P x y) :
    ∃ P' : Base S ⟶ Curve S (W.map σ),
      HasCoordinates S (W.map σ) P' (σ x) (σ y) ∧
      P' ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom σ) ≫ P := by
  let b := Proj.map φ hφ
  let ι := Spec.map (CommRingCat.ofHom σ)
  have hb := isPullback_projMap_of_isCoefficientHom W.toProjective σ φ hφ hcoef
  let P' := hb.lift (ι ≫ P) (𝟙 _) (by
    change (ι ≫ P) ≫ structureMap R W = (𝟙 _) ≫ ι
    rw [Category.assoc, hp.1, Category.comp_id, Category.id_comp])
  have hP' : P' ≫ b = ι ≫ P := hb.lift_fst _ _ _
  have hP'o : P' ≫ structureMap S (W.map σ) = 𝟙 _ := hb.lift_snd _ _ _
  obtain ⟨hPo, χ, hχ, hx, hy⟩ := hp
  have hrange : Set.range P' ⊆ Set.range (chartInclusion S (W.map σ)) := by
    rintro _ ⟨z, rfl⟩
    change P' z ∈ (chartInclusion S (W.map σ)).opensRange
    rw [show (chartInclusion S (W.map σ)).opensRange =
      b ⁻¹ᵁ (chartInclusion R W).opensRange by
        simp only [chartInclusion, zChartι, Proj.opensRange_awayι, b,
          Proj.map_preimage_basicOpen, hcoef.2]]
    change b (P' z) ∈ Set.range (chartInclusion R W)
    rw [← Scheme.Hom.comp_apply, hP', hχ]
    exact ⟨(ι ≫ Spec.map (CommRingCat.ofHom χ)) z, by simp⟩
  let Q := IsOpenImmersion.lift (zChartι (W.map σ).toProjective) P' hrange
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective Q
  have hQ : Spec.map ψ ≫ chartInclusion S (W.map σ) = P' := by
    rw [hψ]
    exact IsOpenImmersion.lift_fac _ _ hrange
  obtain ⟨a, ha, hax, hay⟩ := coefficient_chart W σ φ hφ hcoef
  have he : ψ.hom.comp a = σ.comp χ := by
    change (CommRingCat.ofHom (ψ.hom.comp a)).hom = (CommRingCat.ofHom (σ.comp χ)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    let : Mono (chartInclusion R W) := inferInstanceAs (Mono (zChartι W.toProjective))
    apply (cancel_mono (chartInclusion R W)).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← ha,
      ← Category.assoc, show CommRingCat.ofHom ψ.hom = ψ from rfl, hQ, hP',
      hχ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  refine ⟨P', ⟨hP'o, ψ.hom, hQ.symm, ?_, ?_⟩, hP'⟩
  · have h := RingHom.congr_fun he (xOverZ W.toProjective)
    simpa only [RingHom.comp_apply, hax, hx] using h
  · have h := RingHom.congr_fun he (yOverZ W.toProjective)
    simpa only [RingHom.comp_apply, hay, hy] using h

end CoefficientChange

/-- Transport an isomorphism through two Cartesian squares over the same map. -/
lemma cartesian_iso {X Y X' Y' B B' : Scheme.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (p' : X' ⟶ B') (q' : Y' ⟶ B')
    (ι : B' ⟶ B) (bX : X' ⟶ X) (bY : Y' ⟶ Y)
    (hX : IsPullback bX p' p ι) (hY : IsPullback bY q' q ι)
    (f : X ≅ Y) (hf : f.hom ≫ q = p) :
    ∃ f' : X' ≅ Y', f'.hom ≫ q' = p' ∧ f'.hom ≫ bY = bX ≫ f.hom := by
  have hfi : f.inv ≫ p = q := by rw [← hf, Iso.inv_hom_id_assoc]
  let a := hY.lift (bX ≫ f.hom) p' (by rw [Category.assoc, hf]; exact hX.w)
  let b := hX.lift (bY ≫ f.inv) q' (by rw [Category.assoc, hfi]; exact hY.w)
  have ha1 : a ≫ bY = bX ≫ f.hom := hY.lift_fst _ _ _
  have ha2 : a ≫ q' = p' := hY.lift_snd _ _ _
  have hb1 : b ≫ bX = bY ≫ f.inv := hX.lift_fst _ _ _
  have hb2 : b ≫ p' = q' := hX.lift_snd _ _ _
  refine ⟨⟨a, b, ?_, ?_⟩, ha2, ha1⟩
  · apply hX.hom_ext
    · simp only [Category.assoc, hb1, reassoc_of% ha1, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, hb2, ha2, Category.id_comp]
  · apply hY.hom_ext
    · simp only [Category.assoc, ha1, reassoc_of% hb1, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, ha2, hb2, Category.id_comp]

end OrderedLegendreParameterRigidity

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open OrderedLegendreParameterRigidity

/-- The ordered affine sections force equality of the two Legendre parameters.
The argument applies uniformly at the exceptional j-invariants as well. -/
theorem ordered_legendre_parameter_rigidity :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (lam mu : R), IsUnit (lam * (lam - 1)) → IsUnit (mu * (mu - 1)) → ∀ (p0 p1 : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam))) (q0 q1 : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu))), ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p0 0 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p1 1 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) q0 0 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) q1 1 0 → ∀ f : CategoryTheory.Iso (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu)), CategoryTheory.CategoryStruct.comp (f.hom) (ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu)) = ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) → CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) (f.hom) = ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) → CategoryTheory.CategoryStruct.comp (p0) (f.hom) = q0 → CategoryTheory.CategoryStruct.comp (p1) (f.hom) = q1 → lam = mu := by
  intro R _ _ _ _ _ lam mu _hlam _hmu p0 p1 q0 q1 hp0 hp1 hq0 hq1 f hf ho h0 h1
  let K := FractionRing R
  let σ := algebraMap R K
  let W := legendreAt R lam
  let V := legendreAt R mu
  obtain ⟨φW, hφW, hcW⟩ := exists_isCoefficientHom W.toProjective σ
  obtain ⟨φV, hφV, hcV⟩ := exists_isCoefficientHom V.toProjective σ
  let bW := Proj.map φW hφW
  let bV := Proj.map φV hφV
  have hbW := isPullback_projMap_of_isCoefficientHom W.toProjective σ φW hφW hcW
  have hbV := isPullback_projMap_of_isCoefficientHom V.toProjective σ φV hφV hcV
  obtain ⟨fk, hfko, hfk⟩ := cartesian_iso (structureMap R W) (structureMap R V)
    (structureMap K (W.map σ)) (structureMap K (V.map σ))
    (Spec.map (CommRingCat.ofHom σ)) bW bV hbW hbV f hf
  obtain ⟨pk0, hpk0, ep0⟩ := coefficient_coordinates W σ φW hφW hcW p0 0 0 hp0
  obtain ⟨pk1, hpk1, ep1⟩ := coefficient_coordinates W σ φW hφW hcW p1 1 0 hp1
  obtain ⟨qk0, hqk0, eq0⟩ := coefficient_coordinates V σ φV hφV hcV q0 0 0 hq0
  obtain ⟨qk1, hqk1, eq1⟩ := coefficient_coordinates V σ φV hφV hcV q1 1 0 hq1
  have eoW := coefficient_origin W σ φW hφW hcW
  have eoV := coefficient_origin V σ φV hφV hcV
  have hfko' : fk.hom ≫ projModelStrCR (V.toProjective.map σ) =
      projModelStrCR (W.toProjective.map σ) := hfko
  have hko : origin K (W.map σ) ≫ fk.hom = origin K (V.map σ) := by
    apply hbV.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, eoW, Category.assoc, ho, eoV]
    · rw [Category.assoc, hfko']
      exact (kwZeroSect K (W.map σ)).property.trans (kwZeroSect K (V.map σ)).property.symm
  have hk0 : pk0 ≫ fk.hom = qk0 := by
    apply hbV.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, ep0, Category.assoc, h0, eq0]
    · rw [Category.assoc, hfko']
      exact hpk0.1.trans hqk0.1.symm
  have hk1 : pk1 ≫ fk.hom = qk1 := by
    apply hbV.hom_ext
    · rw [Category.assoc, hfk, ← Category.assoc, ep1, Category.assoc, h1, eq1]
    · rw [Category.assoc, hfko']
      exact hpk1.1.trans hqk1.1.symm
  have h := local_a4 (W.map σ) (V.map σ) pk0 pk1 qk0 qk1
    (by simpa only [map_zero] using hpk0)
    (by simpa only [map_zero, map_one] using hpk1)
    (by simpa only [map_zero] using hqk0)
    (by simpa only [map_zero, map_one] using hqk1) fk hfko hko hk0 hk1
  exact IsFractionRing.injective R K h

#print axioms ordered_legendre_parameter_rigidity
end ArithmeticThetaLegendreComparisonR0177
