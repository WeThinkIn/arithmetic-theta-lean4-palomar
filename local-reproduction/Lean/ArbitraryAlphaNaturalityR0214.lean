import ArbitraryFourCharacterDefinitionsR0214
import ArbitraryFourTorsionRootR0214
import ArbitraryNormalizedFrameUniquenessR0214

/-! Intrinsic alpha over arbitrary rational algebras. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.overlappingInstances false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryAlphaNaturality
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

lemma root_data_unique {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (G : Law R W) (L : ℕ)
    (M : FullLevel R W G L (𝟙 (Base R)))
    {e e' : Fin 3 → R} {x y g x' y' g' : R}
    (h : RootData R W G L M e x y g) (h' : RootData R W G L M e' x' y' g') :
    e = e' ∧ x = x' ∧ y = y' ∧ g = g' := by
  have he : e = e' := funext (fun i => (coordinates_unique W (h.1 i) (h'.1 i)).1)
  obtain ⟨hx, hy⟩ := coordinates_unique W h.2.2.1 h'.2.2.1
  subst e'; subst x'; subst y'
  refine ⟨rfl, rfl, rfl, ?_⟩
  have h2 : IsUnit (2 : R) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ R (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  exact (h2.mul h.2.2.2.1).mul_left_cancel
    (h.2.2.2.2.2.1.trans h'.2.2.2.2.2.1.symm)

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
  (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))

lemma realizes_unique {a a' : Γ(Hodge R W,⊤)}
    (ha : RealizesAlpha R W G L M a) (ha' : RealizesAlpha R W G L M a') : a = a' := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  obtain ⟨e',x',y',g',δ',hr',hδ',rfl⟩ := ha'
  obtain ⟨rfl,rfl,rfl,rfl⟩ := root_data_unique W G L M hr hr'
  rw [arbitrary_normalized_frame_uniqueness R W δ δ' hδ hδ']

lemma realizes_frame {a : Γ(Hodge R W,⊤)}
    (ha : RealizesAlpha R W G L M a) : IsFrame (Hodge R W) ⊤ a := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  apply frame_unit_smul _ _ _ (RelativeNormalizedDifferential.hodge_generator_frame R W δ)
  have h2 : IsUnit (2 : R) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ R (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  exact (h2.mul hr.2.2.2.2.1).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Existence and uniqueness consume both accepted relative constructions. -/
lemma exists_unique_alpha (hG : IsOriginLaw R W G) (hL : 0 < L) (h4 : 4 ∣ L) :
    ∃! a : Γ(Hodge R W,⊤), RealizesAlpha R W G L M a ∧ IsFrame (Hodge R W) ⊤ a := by
  obtain ⟨e,x,y,g,hr⟩ := arbitrary_four_torsion_root R W G hG L hL h4 M
  obtain ⟨δ,hδ⟩ := RelativeNormalizedDifferential.normalized_frame_exists R W
  let a := ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • hodgeGenerator R W δ
  have ha : RealizesAlpha R W G L M a := ⟨e,x,y,g,δ,hr,hδ,rfl⟩
  exact ⟨a,⟨ha,realizes_frame R W G L M ha⟩,
    fun a' ha' => realizes_unique R W G L M ha'.1 ha⟩

lemma hodgeMap_isIso (S : Type u) [CommRing S] (V : WeierstrassCurve S)
    (H : Law S V) (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b) :
    IsIso (hodgeMap R W G S V H ι b hb) := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI := differentialMap_isIso (structureMap R W) (structureMap S V) b hb.1.w hb.1
  unfold hodgeMap
  infer_instance

lemma root_coefficient_covariance {A B : Type u} [CommRing A] [CommRing B]
    [Algebra ℚ B] (ι : A →+* B)
    (e : Fin 3 → A) (es : Fin 3 → B) (x Y g : A) (xs Ys gs : B) (u : Bˣ) (r : B)
    (he : ∀ i, ι (e i) = (u : B)^2 * es i + r)
    (hx : ι x = (u : B)^2 * xs + r) (hY : ι Y = (u : B)^3 * Ys)
    (hYs : IsUnit Ys)
    (hg : 2*Y*g = (x-e 0)^2-(e 0-e 1)*(e 0-e 2))
    (hgs : 2*Ys*gs = (xs-es 0)^2-(es 0-es 1)*(es 0-es 2)) :
    ι g = (u : B)*gs := by
  have h2 : IsUnit (2 : B) := isUnit_iff_exists_inv.mpr
    ⟨algebraMap ℚ B (1/2), TwoTorsionSplitCubicR0177.half_identity⟩
  apply (h2.mul ((u.isUnit.pow 3).mul hYs)).mul_left_cancel
  have h := congrArg ι hg
  rw [map_mul, map_mul, map_ofNat, hY, numerator_covariance ι e es x xs (u : B) r he hx] at h
  linear_combination h - (u : B)^4 * hgs

section Differential
open ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaPullback ArithmeticThetaOpenHodgeR0180
open MvPolynomial
private lemma affine_scalar_injective : Function.Injective (algebraMap R (AffineQuotient R W)) := by
  have hc (a : R) : affineQuotientEquiv R W (algebraMap R W.toAffine.CoordinateRing a) =
      algebraMap R (AffineQuotient R W) a := by
    change affineQuotientEquiv R W (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk _ (C a)
    simp [affineQuotientEquiv, ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv]
  intro a b h
  apply FaithfulSMul.algebraMap_injective R W.toAffine.CoordinateRing
  apply (affineQuotientEquiv R W).injective
  simpa only [hc] using h

private lemma cancel_scalar [Algebra ℚ R] [W.IsElliptic] (r : R)
    (h : zP R W * chartScalar R W r = 0) : r = 0 := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_chart_equiv R W
  have hp : affineQ R W (affinePolyP R W) * algebraMap R (AffineQuotient R W) r = 0 := by
    have hh := congrArg φ h
    simpa only [zP, affinePolyP, map_add, map_mul, map_ofNat, map_zero, hφ, hx, hy,
      show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using hh
  have hd := congrArg (affineTangent R W) hp
  rw [Derivation.leibniz] at hd
  change affineQ R W (affinePolyP R W) * affineTangent R W (algebraMap R (AffineQuotient R W) r) +
    algebraMap R (AffineQuotient R W) r * affineTangent R W (affineQ R W (affinePolyP R W)) =
      affineTangent R W 0 at hd
  rw [Derivation.map_algebraMap, affineTangent_p, map_zero, mul_zero, zero_add] at hd
  have h2 : IsUnit (2 : AffineQuotient R W) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map
      ((algebraMap R (AffineQuotient R W)).comp (algebraMap ℚ R))
  have hq : affineQ R W (affinePolyQ R W) * algebraMap R (AffineQuotient R W) r = 0 := by
    apply h2.mul_right_injective
    linear_combination hd - algebraMap R (AffineQuotient R W) W.a₁ * hp
  have hc := (actual_affine_coprime R W).map φ.toRingHom
  have hc' : IsCoprime (affineQ R W (affinePolyP R W)) (affineQ R W (affinePolyQ R W)) := by
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, zP, zQ,
      affinePolyP, affinePolyQ, map_add, map_sub, map_mul, map_pow, map_ofNat, hφ, hx, hy,
      show ∀ a, affineQ R W (C a) = algebraMap R (AffineQuotient R W) a from fun _ => rfl] using hc
  obtain ⟨a,b,hab⟩ := hc'
  apply affine_scalar_injective R W
  rw [map_zero]
  calc
    algebraMap R (AffineQuotient R W) r = (a * affineQ R W (affinePolyP R W) +
        b * affineQ R W (affinePolyQ R W)) * algebraMap R (AffineQuotient R W) r := by rw [hab, one_mul]
    _ = 0 := by rw [add_mul, mul_assoc, mul_assoc, hp, hq]; ring

private def curveScalarLocal (r : R) : Γ(Curve R W, ⊤) :=
  (structureMap R W).constToPresheaf.app (Opposite.op ⊤) r

private lemma scalar_surjective : Function.Surjective (curveScalarLocal R W) := by
  have hf := P2MW.S_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR.WeierstrassProjModel.K1bReduce.bijective_appTop_projModelStrCR W.toProjective
  exact hf.2.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2

private lemma scalar_restrict (r : R) :
    (Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op (curveScalarLocal R W r) =
      zSection R W (chartScalar R W r) := by
  have h := CategoryTheory.congr_fun ((structureMap R W).constToPresheaf.naturality
    (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op) r
  have he : (Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op (curveScalarLocal R W r) =
      (structureMap R W).constToPresheaf.app (Opposite.op (zOpen R W)) r := h.symm
  rw [he]
  letI : Algebra R (ChartRing R W) := (chartScalar R W).toAlgebra
  letI := (structureMap R W).sectionsAlgebra (zOpen R W)
  apply (chartRingEquiv (chartInclusion R W)).injective
  rw [RingEquiv.apply_symm_apply]
  exact chartRingEquiv_algebraMap (structureMap R W) (chartInclusion R W) (chart_structure R W) r

private lemma weighted_section_ext (δ : CurveFrame R W)
    (s t : Γ((structureMap R W).kaehler, ⊤))
    (hm : zSection R W (zP R W) • res (structureMap R W).kaehler
        (show zOpen R W ≤ ⊤ from le_top) t =
      zSection R W (zP R W) • res (structureMap R W).kaehler
        (show zOpen R W ≤ ⊤ from le_top) s) : t = s := by
  let U := zOpen R W
  let a : Γ(Curve R W, ⊤) := Scheme.Modules.Hom.app δ.inv ⊤ (t-s)
  obtain ⟨r, hr⟩ := scalar_surjective R W a
  have ha : (Curve R W).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
      Scheme.Modules.Hom.app δ.inv U
        (res (structureMap R W).kaehler (show U ≤ ⊤ from le_top) t -
          res (structureMap R W).kaehler (show U ≤ ⊤ from le_top) s) := by
    have hh := hom_restrict δ.inv ⊤ U le_top (t-s)
    exact hh.trans (congrArg (Scheme.Modules.Hom.app δ.inv U)
      (map_sub ((structureMap R W).kaehler.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom t s))
  have hz : zSection R W (zP R W) *
      ((Curve R W).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) = 0 := by
    rw [ha]
    have hh := congrArg (Scheme.Modules.Hom.app δ.inv U) hm
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at hh
    rw [map_sub]
    change zSection R W (zP R W) *
      ((show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _) -
        (show Γ(Curve R W,U) from Scheme.Modules.Hom.app δ.inv U _)) = 0
    rw [mul_sub]
    exact sub_eq_zero.mpr hh
  have hr0 : r = 0 := by
    apply cancel_scalar R W r
    apply (zSection R W).injective
    rw [map_mul, map_zero]
    rw [← scalar_restrict, hr]
    exact hz
  have ha0 : a = 0 := by
    rw [← hr, hr0]
    exact map_zero _
  have hts : t = s := by
    apply sub_eq_zero.mp
    apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app δ.inv ⊤)).1
    exact ha0.trans (map_zero _).symm
  exact hts
lemma normalized_on_open (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W)
      (RelativeNormalizedDifferential.zOpen R W)
      (RelativeNormalizedDifferential.zSection R W (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective)) =
    RelativeNormalizedDifferential.zSection R W (RelativeNormalizedDifferential.zP R W) •
      res (structureMap R W).kaehler le_top (differentialSection R W δ) := by
  obtain ⟨ε,hεx,hεy⟩ := RelativeNormalizedDifferential.global_frame_on_open R W
  have he := RelativeNormalizedDifferential.normalized_of_open R W ε hεx
  have hEq := arbitrary_normalized_frame_uniqueness R W ε δ he hδ
  subst δ
  rw [hεx]
  congr 1
  exact (ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.frame_section_restrict
    (structureMap R W) ε ⊤ (RelativeNormalizedDifferential.zOpen R W) le_top).symm

variable (S : Type u) [CommRing S] (Ws : WeierstrassCurve S)
  (Gs : Law S Ws) (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b)
def pullDifferential (s : Γ((structureMap R W).kaehler,⊤)) : Γ((structureMap S Ws).kaehler,⊤) := by
  letI : Algebra R S := ι.toAlgebra
  exact (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app ⊤
    (pullbackGlobalSection b (structureMap R W).kaehler s)

lemma pull_hodge_generator (δ : CurveFrame R W) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S Ws Gs ι b hb (hodgeGenerator R W δ) =
      pullbackGlobalSection (origin S Ws) (structureMap S Ws).kaehler
        (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) := by
  letI : Algebra R S := ι.toAlgebra
  change ((Scheme.Modules.pullback (origin S Ws)).map
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w)).app ⊤
    ((squarePullbackIso (baseMap R S ι) (origin R W) (origin S Ws) b hb.2.1.symm
      (structureMap R W).kaehler).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (baseMap R S ι)
        (Scheme.Modules.pullbackLocalSection (origin R W) (differentialSection R W δ)))) = _
  have hsq := squarePullbackIso_section (baseMap R S ι) (origin R W) (origin S Ws) b
    hb.2.1.symm (structureMap R W).kaehler ⊤ (differentialSection R W δ) ⊤ le_top le_top
  simp only [res_refl] at hsq
  erw [hsq]
  exact (Scheme.Modules.pullbackLocalSection_app (origin S Ws)
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w)
    (Scheme.Modules.pullbackLocalSection b (differentialSection R W δ))).symm

lemma pull_differential_equation
    (U : (Curve R W).Opens) (x p : Γ(Curve R W,U))
    (s : Γ((structureMap R W).kaehler,⊤))
    (hn : ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U x =
      p • res (structureMap R W).kaehler le_top s) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws) (b ⁻¹ᵁ U) (b.app U x) =
      b.app U p • res (structureMap S Ws).kaehler le_top (pullDifferential R W G S Ws Gs ι b hb s) := by
  letI : Algebra R S := ι.toAlgebra
  have hh := congrArg (fun t =>
    (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b t)) hn
  rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_D, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul] at hh
  rw [hh]
  congr 1
  change (differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b (res (structureMap R W).kaehler le_top s)) =
    res (structureMap S Ws).kaehler le_top
      ((differentialMap (structureMap R W) (structureMap S Ws) b hb.1.w).app ⊤
        (Scheme.Modules.pullbackLocalSection b s))
  rw [hom_res]
  congr 1
  exact (Scheme.Modules.map_homOfLE_pullbackLocalSection b (show U ≤ ⊤ from le_top) s).symm

lemma pull_differential_on_chart
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (δ : CurveFrame R W) (hδ : NormalizedFrame R W δ) :
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws)
      (RelativeNormalizedDifferential.zOpen S Ws)
      (RelativeNormalizedDifferential.zSection S Ws (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective))) =
    RelativeNormalizedDifferential.zSection S Ws (χ (RelativeNormalizedDifferential.zP R W)) •
      res (structureMap S Ws).kaehler le_top
        (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) := by
  have h := pull_differential_equation R W G S Ws Gs ι b hb _ _ _ _ (normalized_on_open R W δ hδ)
  have hr := congrArg (res (structureMap S Ws).kaehler (chart_preimage W Ws b χ hχ)) h
  rw [relativeD_res,res_smul,res_res] at hr
  change ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap S Ws)
      (RelativeNormalizedDifferential.zOpen S Ws)
      (b.appLE _ _ (chart_preimage W Ws b χ hχ) _) =
    b.appLE _ _ (chart_preimage W Ws b χ hχ) _ • res (structureMap S Ws).kaehler le_top _ at hr
  rw [chart_section_natural W Ws b χ hχ,chart_section_natural W Ws b χ hχ] at hr
  exact hr

lemma differential_weight [Algebra ℚ S] [Ws.IsElliptic]
    (C : WeierstrassCurve.VariableChange S) (hC : C • W.map ι = Ws)
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (hc : ∀ a, χ (chartScalar R W a) = chartScalar S Ws (ι a))
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^2)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.r)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^3)*WeierstrassCurve.DrinfeldGlobal.yOverZ Ws.toProjective +
      chartScalar S Ws ((C.u : S)^2*C.s)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.t)
    (δ : CurveFrame R W) (δs : CurveFrame S Ws)
    (hδ : NormalizedFrame R W δ) (hδs : NormalizedFrame S Ws δs) :
    pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ) =
      curveScalar Ws (↑(C.u⁻¹) : S) • differentialSection S Ws δs := by
  let U := RelativeNormalizedDifferential.zOpen S Ws
  let z := RelativeNormalizedDifferential.zSection S Ws
  let p := z (RelativeNormalizedDifferential.zP S Ws)
  let c := z (chartScalar S Ws (C.u : S))
  let ci := z (chartScalar S Ws (↑(C.u⁻¹) : S))
  have hunit : IsUnit c := (C.u.isUnit.map (chartScalar S Ws)).map z.toRingHom
  have hinv : c*ci = 1 := by
    dsimp [c,ci]
    rw [← map_mul,← map_mul,Units.mul_inv,map_one,map_one]
  have h := pull_differential_on_chart R W G S Ws Gs ι b hb χ hχ δ hδ
  rw [hx,map_add,map_mul,
    ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.relativeD_add,
    ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.relativeD_mul,
    relativeD_zsection_scalar,relativeD_zsection_scalar,smul_zero,add_zero,add_zero,
    normalized_on_open S Ws δs hδs,chart_ordinate_weight W Ws ι C hC χ hc hx hy,
    map_mul,map_pow,map_pow,map_pow,map_pow,smul_smul] at h
  change (c^2*p) • res (structureMap S Ws).kaehler le_top (differentialSection S Ws δs) =
    (c^3*p) • res (structureMap S Ws).kaehler le_top
      (pullDifferential R W G S Ws Gs ι b hb (differentialSection R W δ)) at h
  apply weighted_section_ext S Ws δs
  rw [res_smul, curve_scalar_restrict, ← zsection_scalar, smul_smul]
  have hh := congrArg (fun v => ci^3 • v) h
  simp only [smul_smul] at hh
  have hleft : ci^3*(c^2*p) = p*ci := by
    linear_combination p*ci*(c*ci+1)*(hinv)
  have hright : ci^3*(c^3*p) = p := by
    linear_combination p*((c*ci)^2+c*ci+1)*(hinv)
  rw [hleft, hright] at hh
  exact hh.symm

lemma hodge_differential_weight [Algebra ℚ S] [Ws.IsElliptic]
    (C : WeierstrassCurve.VariableChange S) (hC : C • W.map ι = Ws)
    (χ : ChartRing R W →+* ChartRing S Ws)
    (hχ : chartInclusion S Ws ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W)
    (hc : ∀ a, χ (chartScalar R W a) = chartScalar S Ws (ι a))
    (hx : χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^2)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.r)
    (hy : χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
      chartScalar S Ws ((C.u : S)^3)*WeierstrassCurve.DrinfeldGlobal.yOverZ Ws.toProjective +
      chartScalar S Ws ((C.u : S)^2*C.s)*WeierstrassCurve.DrinfeldGlobal.xOverZ Ws.toProjective + chartScalar S Ws C.t)
    (δ : CurveFrame R W) (δs : CurveFrame S Ws)
    (hδ : NormalizedFrame R W δ) (hδs : NormalizedFrame S Ws δs) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S Ws Gs ι b hb (hodgeGenerator R W δ) =
      scalar S (↑(C.u⁻¹) : S) • hodgeGenerator S Ws δs := by
  rw [pull_hodge_generator,differential_weight R W G S Ws Gs ι b hb C hC χ hχ hc hx hy δ δs hδ hδs]
  change Scheme.Modules.pullbackLocalSection (origin S Ws)
    (curveScalar Ws (↑(C.u⁻¹) : S) • differentialSection S Ws δs) = _
  rw [Scheme.Modules.pullbackLocalSection_smul,origin_curve_scalar]
  rfl

lemma scalar_pullback (v : R) :
    (baseMap R S ι).app ⊤ (scalar R v) = scalar S (ι v) := by
  change (baseMap R S ι).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv v) =
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι v)
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι)
  exact (CategoryTheory.congr_fun h v).symm

lemma pull_alpha_smul (v : R) (a : Γ(Hodge R W,⊤)) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S Ws Gs ι b hb (scalar R v • a) =
      scalar S (ι v) • ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S Ws Gs ι b hb a := by
  unfold ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha
  change (hodgeMap R W G S Ws Gs ι b hb).app ⊤
    (Scheme.Modules.pullbackLocalSection (baseMap R S ι) (scalar R v • a)) = _
  rw [Scheme.Modules.pullbackLocalSection_smul, scalar_pullback R S ι,
    Scheme.Modules.Hom.app_smul]
  rfl

end Differential

section LocalCharts
open ArithmeticThetaLegendreComparisonR0177.NormalFormConstruction
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts
open VariableChange.WMLocal
open HomogeneousLocalization IsLocalRing in
theorem local_variable_change
    (T : Type u) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit W'.Δ)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by
  classical

  obtain ⟨e, hec, heι⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartEquiv.solution T W W' Ψ hΨ hΨO

  obtain ⟨Φ, hΦc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W
  obtain ⟨lam, hlc, hlx, hly, hF2, hF3⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentFiltration.solution T W Φ hΦc hΦx hΦz

  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.LaurentCoeff.solution T W W' Ψ hΨ hΨO
    e.toRingHom heι Φ hΦc hΦx hΦz lam hlc hlx hly

  obtain ⟨v₁, v₂, r, s', t, hex, hey⟩ := VariableChange.WMLocal.triangular_of_coeff (VariableChange.WMLocal.cZ W) (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e.toRingHom lam hF2 hF3 hx₁ hx₂ hy₁ hy₂

  obtain ⟨g, hgx, hgy⟩ := VariableChange.WMLocal.exists_coordinateRing_algHom_triangular_of_zChart_ringEquiv W W' e hec v₁ v₂ r s' t hex hey
  obtain ⟨ex, ey⟩ := VariableChange.WMLocal.symm_triangular (VariableChange.WMLocal.cZ W) (VariableChange.WMLocal.cZ W') (xOverZ W.toProjective)
    (yOverZ W.toProjective) (xOverZ W'.toProjective) (yOverZ W'.toProjective) e hec v₁ v₂ r s' t hex hey
  generalize hw₁ : v₁⁻¹ = w₁ at hgx hgy ex ey
  generalize hw₂ : v₂⁻¹ = w₂ at hgx hgy ex ey
  generalize hr₁ : (-(↑w₁ * r) : T) = r₁ at hgx ex
  generalize hs₁ : (-(↑w₂ * s' * ↑w₁) : T) = s₁ at hgy ey
  generalize ht₁ : (↑w₂ * (s' * ↑w₁ * r - t) : T) = t₁ at hgy ey
  obtain ⟨C, hC, ⟨hu2, hu3⟩, hCr, hCs, hCt⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.Triangular.solution T W W' g w₁ w₂ r₁ s₁ t₁ hgx hgy
  subst hC

  obtain ⟨φ, hφ, hvc, _, _⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W.toProjective C
  refine ⟨C, rfl, φ, hφ, hvc, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]

  obtain ⟨a, haι, hac, hax, hay⟩ := WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom W.toProjective C φ hφ hvc
  have hec' : ∀ b : T, e.symm (VariableChange.WMLocal.cZ W b) = VariableChange.WMLocal.cZ (C • W) b := fun b => by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hec b).symm
  have hae : a = e.symm.toRingHom := by
    apply VariableChange.WMLocal.zChart_ringHom_ext W.toProjective
    · refine RingHom.ext fun b => ?_
      change a (VariableChange.WMLocal.cZ W b) = e.symm (VariableChange.WMLocal.cZ W b)
      rw [hec']
      exact hac b
    · change a (xOverZ W.toProjective) = e.symm (xOverZ W.toProjective)
      rw [hax, ex, hu2, hCr]
      rfl
    · change a (yOverZ W.toProjective) = e.symm (yOverZ W.toProjective)
      rw [hay, ey, hCs, hu3, hCt]
      rfl
  apply ArithmeticThetaMarkedGroupLawR0146.ActualScalarTranslation.UniversePorts.ChartExt.solution T (C • W)
  rw [haι, hae]

  have hcomp : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun z => ?_
    show e.symm (e z) = z
    exact e.symm_apply_apply z
  have hee : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp, Spec.map_id]
  symm
  calc zChartι (C • W).toProjective ≫ Ψ.inv
      = (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
          zChartι (C • W).toProjective ≫ Ψ.inv := by rw [hee, Category.id_comp]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι (C • W).toProjective) ≫ Ψ.inv) := by
        simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ((zChartι W.toProjective ≫ Ψ.hom) ≫ Ψ.inv) := by rw [heι]
    _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ zChartι W.toProjective := by
        rw [Category.assoc, Ψ.hom_inv_id, Category.comp_id]


lemma pointed_local_iso_chart {T : Type u} [CommRing T] [IsLocalRing T]
    (W V : WeierstrassCurve T) [W.IsElliptic] [V.IsElliptic]
    (f : Curve T V ≅ Curve T W)
    (hf : f.hom ≫ structureMap T W = structureMap T V)
    (ho : origin T V ≫ f.hom = origin T W) :
    ∃ (C : WeierstrassCurve.VariableChange T) (χ : ChartRing T W →+* ChartRing T V),
      C • W = V ∧
      chartInclusion T V ≫ f.hom = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion T W ∧
      (∀ a, χ (chartScalar T W a) = chartScalar T V a) ∧
      χ (xOverZ W.toProjective) =
        chartScalar T V ((C.u : T)^2) * xOverZ V.toProjective + chartScalar T V C.r ∧
      χ (yOverZ W.toProjective) =
        chartScalar T V ((C.u : T)^3) * yOverZ V.toProjective +
        chartScalar T V ((C.u : T)^2*C.s) * xOverZ V.toProjective + chartScalar T V C.t := by
  have hfi : f.inv ≫ structureMap T V = structureMap T W := by
    rw [← hf, Iso.inv_hom_id_assoc]
  have hoi : origin T W ≫ f.inv = origin T V := by
    rw [← ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨C,hC,φ,hφ,hvc,hmap⟩ :=
    local_variable_change
      T W V W.isUnit_Δ V.isUnit_Δ f.symm hfi hoi
  subst V
  simp only [eqToHom_refl, Category.id_comp] at hmap
  obtain ⟨χ,hχ,hχc,hχx,hχy⟩ :=
    exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
      W.toProjective C φ hφ hvc
  rw [hmap] at hχ
  exact ⟨C,χ,rfl,hχ,by simpa only [chartScalar_apply] using hχc,
    by simpa only [chartScalar_apply] using hχx,
    by simpa only [chartScalar_apply] using hχy⟩

lemma cartesian_local_chart {A F : Type u} [CommRing A] [CommRing F] [IsLocalRing F]
    (W : WeierstrassCurve A) [W.IsElliptic] (V : WeierstrassCurve F) [V.IsElliptic]
    (ι : A →+* F) (b : Curve F V ⟶ Curve A W)
    (hb : IsPullback b (structureMap F V) (structureMap A W) (baseMap A F ι))
    (ho : origin F V ≫ b = baseMap A F ι ≫ origin A W) :
    ∃ (C : WeierstrassCurve.VariableChange F) (χ : ChartRing A W →+* ChartRing F V),
      C • W.map ι = V ∧
      chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W ∧
      (∀ a, χ (chartScalar A W a) = chartScalar F V (ι a)) ∧
      χ (xOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^2) * xOverZ V.toProjective + chartScalar F V C.r ∧
      χ (yOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^3) * yOverZ V.toProjective +
        chartScalar F V ((C.u : F)^2*C.s) * xOverZ V.toProjective + chartScalar F V C.t := by
  obtain ⟨φ,hφ,hcoef⟩ := exists_isCoefficientHom W.toProjective ι
  let c := Proj.map φ hφ
  have hc := isPullback_projMap_of_isCoefficientHom W.toProjective ι φ hφ hcoef
  obtain ⟨f,hf,hfc⟩ := OrderedLegendreParameterRigidity.cartesian_iso
    (structureMap A W) (structureMap A W) (structureMap F V) (structureMap F (W.map ι))
    (baseMap A F ι) b c hb hc (Iso.refl _) (by simp)
  simp only [Iso.refl_hom, Category.comp_id] at hfc
  have hfo : origin F V ≫ f.hom = origin F (W.map ι) := by
    apply hc.hom_ext
    · rw [Category.assoc, hfc, ho]
      exact (OrderedLegendreParameterRigidity.coefficient_origin W ι φ hφ hcoef).symm
    · change (origin F V ≫ f.hom) ≫ structureMap F (W.map ι) =
        origin F (W.map ι) ≫ structureMap F (W.map ι)
      rw [Category.assoc, hf]
      exact (kwZeroSect F V).property.trans (kwZeroSect F (W.map ι)).property.symm
  obtain ⟨C,ψ,hC,hψ,hψc,hψx,hψy⟩ := pointed_local_iso_chart (W.map ι) V f hf hfo
  obtain ⟨a,ha,hax,hay⟩ := OrderedLegendreParameterRigidity.coefficient_chart W ι φ hφ hcoef
  let χ := ψ.comp a
  have hχ : chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion A W := by
    rw [← hfc, ← Category.assoc, hψ, Category.assoc, ha,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨C,χ,hC,hχ,chart_scalar_natural W V ι b hb.w χ hχ,?_,?_⟩
  · simpa only [χ,RingHom.comp_apply,hax] using hψx
  · simpa only [χ,RingHom.comp_apply,hay] using hψy

end LocalCharts

lemma labels_sum {e : Fin 3 → R} {x y g : R} (h : RootData R W G L M e x y g) :
    W.a₂ + algebraMap ℚ R (1/4)*W.a₁^2 = -(e 0+e 1+e 2) := by
  exact (ArithmeticThetaArbitraryAffineR0202.ArbitrarySplitCubic.cubic_coefficients
    (W.a₂ + algebraMap ℚ R (1/4)*W.a₁^2)
    (W.a₄ + algebraMap ℚ R (1/2)*W.a₁*W.a₃)
    (W.a₆ + algebraMap ℚ R (1/4)*W.a₃^2)
    (e 0) (e 1) (e 2)
    (h.2.1.1 0 1 (by decide)) (h.2.1.1 1 2 (by decide)) (h.2.1.1 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 0))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 1))
    (TwoTorsionSplitCubicR0177.root_equation (h.1 2))).1

open ArithmeticThetaPullback ArithmeticThetaOpenHodgeR0180
lemma local_root_weight (F : Type u) [CommRing F] [IsLocalRing F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (N : FullLevel F V H L (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hMx : N.x.val ≫ b = baseMap R F ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R F ι ≫ M.y.val)
    (e : Fin 3 → R) (es : Fin 3 → F) (x y g : R) (xs ys gs : F)
    (hr : RootData R W G L M e x y g) (hs : RootData F V H L N es xs ys gs) :
    ∃ (C : WeierstrassCurve.VariableChange F) (χ : ChartRing R W →+* ChartRing F V),
      C • W.map ι = V ∧
      chartInclusion F V ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
      (∀ a, χ (chartScalar R W a) = chartScalar F V (ι a)) ∧
      χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^2) * WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective + chartScalar F V C.r ∧
      χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
        chartScalar F V ((C.u : F)^3) * WeierstrassCurve.DrinfeldGlobal.yOverZ V.toProjective +
        chartScalar F V ((C.u : F)^2*C.s) * WeierstrassCurve.DrinfeldGlobal.xOverZ V.toProjective + chartScalar F V C.t ∧
      ι g = (C.u : F)*gs := by
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy⟩ := cartesian_local_chart W V ι b hb.1 hb.2.1
  have hn (P : NeronModelInfra.SchemeHomOver (𝟙 (Base R)) (structureMap R W))
      (Q : NeronModelInfra.SchemeHomOver (𝟙 (Base F)) (structureMap F V))
      (hPQ : Q.val ≫ b = baseMap R F ι ≫ P.val) (n : ℕ) :
      (H.nsmul (𝟙 _) n Q).val ≫ b = baseMap R F ι ≫ (G.nsmul (𝟙 _) n P).val := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.assoc,hb.2.2,← Category.assoc,hPQ,Category.assoc]
  have h0 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.x N.x hMx (L/2))
    _ _ _ _ (hr.1 0) (hs.1 0) (C.u : F) C.r C.s C.t hχx hχy
  have h1 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hMy (L/2))
    _ _ _ _ (hr.1 1) (hs.1 1) (C.u : F) C.r C.s C.t hχx hχy
  have hq := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hMy (L/4))
    _ _ _ _ hr.2.2.1 hs.2.2.1 (C.u : F) C.r C.s C.t hχx hχy
  have ha := congrArg ι (labels_sum R W G L M hr)
  simp only [map_add,map_mul,map_pow,map_neg,rational_map] at ha
  have has := labels_sum F V H L N hs
  have hc2 := completed_a2_variable (W.map ι) C
  rw [hC] at hc2
  change ι W.a₂ + algebraMap ℚ F (1/4)*(ι W.a₁)^2 + 3*C.r =
    (C.u : F)^2*(V.a₂+algebraMap ℚ F (1/4)*V.a₁^2) at hc2
  have he2 : ι (e 2) = (C.u : F)^2*es 2+C.r := by
    linear_combination ha - hc2 - h0.1 - h1.1 - (C.u : F)^2*has
  have he (i : Fin 3) : ι (e i) = (C.u : F)^2*es i+C.r := by
    fin_cases i
    · exact h0.1
    · exact h1.1
    · exact he2
  have hY : ι (completedY R W x y) = (C.u : F)^3*completedY F V xs ys := by
    rw [completed_y_map,hq.1,hq.2,completed_y_variable,hC]
  exact ⟨C,χ,hC,hχ,hχc,hχx,hχy,
    root_coefficient_covariance ι e es x (completedY R W x y) g xs
      (completedY F V xs ys) gs C.u C.r he hq.1 hY hs.2.2.2.1
      hr.2.2.2.2.2.1 hs.2.2.2.2.2.1⟩

lemma alpha_local_naturality (F : Type u) [CommRing F] [IsLocalRing F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (N : FullLevel F V H L (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hMx : N.x.val ≫ b = baseMap R F ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R F ι ≫ M.y.val)
    (a : Γ(Hodge R W,⊤)) (af : Γ(Hodge F V,⊤))
    (ha : RealizesAlpha R W G L M a) (haf : RealizesAlpha F V H L N af) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G F V H ι b hb a = af := by
  obtain ⟨e,x,y,g,δ,hr,hδ,rfl⟩ := ha
  obtain ⟨es,xs,ys,gs,δs,hs,hδs,rfl⟩ := haf
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy,hg⟩ := local_root_weight R W G L M F V H N ι b hb
    hMx hMy e es x y g xs ys gs hr hs
  rw [pull_alpha_smul,hodge_differential_weight R W G F V H ι b hb C hC χ hχ hχc hχx hχy δ δs hδ hδs,
    smul_smul]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of F)).inv (ι (2*g)) *
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv (↑(C.u⁻¹) : F) =
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv (2*gs)
  rw [← map_mul]
  congr 1
  rw [map_mul,map_ofNat,hg]
  calc
    2*((C.u : F)*gs)*↑(C.u⁻¹) = 2*gs*((C.u : F)*↑(C.u⁻¹)) := by ring
    _ = 2*gs := by rw [Units.mul_inv,mul_one]

section Composition
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
variable (S : Type u) [CommRing S] [Algebra ℚ S]
  (V : WeierstrassCurve S) [V.IsElliptic] (H : Law S V)
  (T : Type u) [CommRing T] (Z : WeierstrassCurve T) (J : Law T Z)
  (ι : R →+* S) (κ : S →+* T) (b : Curve S V ⟶ Curve R W) (c : Curve T Z ⟶ Curve S V)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
  (hc : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange S V H T Z J κ c)
  (hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G T Z J (κ.comp ι) (c ≫ b))
lemma hodge_comparison_comp :
    hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd =
      composeComparison (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
        (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ))
        (Hodge R W) (Hodge S V) (Hodge T Z)
        (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc) := by
  have hf : ∀ t : Base R, ∃ (U : (Curve R W).Opens) (a : Γ(Curve R W,U)),
      origin R W t ∈ U ∧ IsFrame (Hodge R W) (origin R W ⁻¹ᵁ U) (localDifferential R W U a) := by
    letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
      WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
    intro t
    obtain ⟨U,a,ht,hf⟩ := exists_exact_differential_frame (structureMap R W) (origin R W t)
    exact ⟨U,a,ht,pullback_frame _ _ _ hf⟩
  exact local_comparison_comp (origin R W) (origin S V) (origin T Z)
    (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
    (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ)) b c hb.2.1 hc.2.1 hd.2.1
    (Hodge R W) (Hodge S V) (Hodge T Z)
    (localDifferential R W) (localDifferential S V) (localDifferential T Z) hf
    (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc)
    (hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd)
    (hodgeIso_D R W G S V H ι b hb) (hodgeIso_D S V H T Z J κ c hc)
    (hodgeIso_D R W G T Z J (κ.comp ι) (c ≫ b) hd)

set_option maxHeartbeats 200000 in
lemma pull_alpha_comp (a : Γ(Hodge R W,⊤)) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G T Z J (κ.comp ι) (c ≫ b) hd a =
      ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha S V H T Z J κ c hc (ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S V H ι b hb a) := by
  unfold ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha
  exact global_comparison_comp (baseMap R S ι) (baseMap S T κ) (baseMap R T (κ.comp ι))
    (Spec.map_comp (CommRingCat.ofHom ι) (CommRingCat.ofHom κ))
    (Hodge R W) (Hodge S V) (Hodge T Z)
    (hodgeIso R W G S V H ι b hb) (hodgeIso S V H T Z J κ c hc)
    (hodgeIso R W G T Z J (κ.comp ι) (c ≫ b) hd)
    (hodge_comparison_comp R W G S V H T Z J ι κ b c hb hc hd) a

end Composition
section CoefficientModel
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

/-- The actual coefficient model carries the transported law and pointed Cartesian map. -/
lemma coefficient_base_change (hG : IsOriginLaw R W G)
    (S : Type u) [CommRing S] (ι : R →+* S) :
    ∃ (H : Law S (W.map ι)) (b : Curve S (W.map ι) ⟶ Curve R W),
      IsOriginLaw S (W.map ι) H ∧
      ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S (W.map ι) H ι b := by
  obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom W.toProjective ι
  let b := Proj.map φ hφ
  have hb := isPullback_projMap_of_isCoefficientHom W.toProjective ι φ hφ hcoef
  have he : origin S (W.map ι) ≫ b = baseMap R S ι ≫ origin R W :=
    OrderedLegendreParameterRigidity.coefficient_origin W ι φ hφ hcoef
  obtain ⟨H, hm, ho⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    ι (structureMap R W) (structureMap S (W.map ι)) b hb G
  have hH : IsOriginLaw S (W.map ι) H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · change (H.one t).val ≫ b = (t ≫ origin S (W.map ι)) ≫ b
        simp only [ho, hG.1, Category.assoc, he, baseMap]
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z) (kwZeroSect S (W.map ι)).property).trans
            (Category.comp_id t)).symm)
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  exact ⟨H, b, hH, hb, he,
    ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp
      ι (structureMap S (W.map ι)) b hb G H hm ho⟩
end CoefficientModel

/-- Naturality is checked in localizations, which retain nilpotents, and
then descended by faithful localization of the scalar coefficient of a frame. -/
lemma alpha_naturality (hG : IsOriginLaw R W G) (hL : 0 < L) (h4 : 4 ∣ L)
    (S : Type u) [CommRing S] [Algebra ℚ S]
    (V : WeierstrassCurve S) [V.IsElliptic] (H : Law S V) (hH : IsOriginLaw S V H)
    (N : FullLevel S V H L (𝟙 (Base S)))
    (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (hMx : N.x.val ≫ b = baseMap R S ι ≫ M.x.val)
    (hMy : N.y.val ≫ b = baseMap R S ι ≫ M.y.val)
    (a : Γ(Hodge R W,⊤)) (as_ : Γ(Hodge S V,⊤))
    (ha : RealizesAlpha R W G L M a) (has : RealizesAlpha S V H L N as_) :
    ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S V H ι b hb a = as_ := by
  have hf := realizes_frame S V H L N has
  obtain ⟨v, hv⟩ := (hf ⊤ le_rfl).2
    (ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S V H ι b hb a)
  simp only [res_refl] at hv
  let r : S := (Scheme.ΓSpecIso (CommRingCat.of S)).hom v
  have hr : scalar S r = v :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id v
  have hr1 : r = 1 := by
    apply Module.eq_of_localization_maximal
      (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap S (Localization.AtPrime P))
    intro P hP
    let K := Localization.AtPrime P
    let κ : S →+* K := algebraMap S K
    let Z := V.map κ
    obtain ⟨J, c, hJ, hc⟩ := coefficient_base_change S V H hH K κ
    have hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
        R W G K Z J (κ.comp ι) (c ≫ b) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [CommRingCat.ofHom_comp, Spec.map_comp]
        exact hc.1.paste_horiz hb.1
      · rw [← Category.assoc, hc.2.1, Category.assoc, hb.2.1,
          CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      · intro n
        rw [← Category.assoc, hc.2.2, Category.assoc, hb.2.2, Category.assoc]
    let B : FullLevel S V H L ((𝟙 (Base K)) ≫ baseMap S K κ) :=
      BaseChange.restrict N (baseMap S K κ) (by simp)
    let Nk : FullLevel K Z J L (𝟙 (Base K)) := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up hc hH hJ B
    have hNx : Nk.x.val ≫ c = baseMap S K κ ≫ N.x.val := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_x hc hH hJ B
    have hNy : Nk.y.val ≫ c = baseMap S K κ ≫ N.y.val := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_y hc hH hJ B
    have hKx : Nk.x.val ≫ (c ≫ b) = baseMap R K (κ.comp ι) ≫ M.x.val := by
      rw [← Category.assoc, hNx, Category.assoc, hMx]
      simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hKy : Nk.y.val ≫ (c ≫ b) = baseMap R K (κ.comp ι) ≫ M.y.val := by
      rw [← Category.assoc, hNy, Category.assoc, hMy]
      simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    obtain ⟨ak, hak, _⟩ := exists_unique_alpha K Z J L Nk hJ hL h4
    have he : ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha S V H K Z J κ c hc
        (ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S V H ι b hb a) =
      ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha S V H K Z J κ c hc as_ := by
      rw [← pull_alpha_comp R W G S V H K Z J ι κ b c hb hc hd a,
        alpha_local_naturality R W G L M K Z J Nk (κ.comp ι) (c ≫ b) hd hKx hKy a ak ha hak.1,
        alpha_local_naturality S V H L N K Z J Nk κ c hc hNx hNy as_ ak has hak.1]
    have hpf : IsFrame (Hodge K Z) ⊤
        (ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha S V H K Z J κ c hc as_) :=
      ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
        (hodgeIso S V H K Z J κ c hc) _ (pullback_frame _ _ _ hf)
    rw [← hv, ← hr, pull_alpha_smul] at he
    have he' : scalar K (κ r) = scalar K (1 : K) := (hpf ⊤ le_rfl).1 (by
      simpa only [res_refl, scalar, map_one, one_smul] using he)
    have he'' := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 he'
    simpa only [Algebra.linearMap_apply, map_one] using he''
  rw [← hv, ← hr, hr1]
  simp only [scalar, map_one, one_smul]

end ArbitraryAlphaNaturality

/-- The intrinsic alpha frame and its canonical pointed Cartesian naturality,
including nonreduced, disconnected, non-Noetherian and zero bases. -/
theorem arbitrary_alpha_naturality :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), (∃! a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W) ⊤ a) ∧ (∀ (S : Type u) [CommRing S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (Ms : ArithmeticThetaFullLevelCoverR0175.FullLevel S Ws Gs L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b), CategoryTheory.IsIso (ArithmeticThetaArbitraryFourCharacterR0214.hodgeMap R W G S Ws Gs ι b hb) ∧ (CategoryTheory.CategoryStruct.comp (Ms.x.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.x.val) → CategoryTheory.CategoryStruct.comp (Ms.y.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.y.val) → ∀ (a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤)) (as_ : (ArithmeticThetaRelativeDiscriminantR0171.Hodge S Ws).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a → ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha S Ws Gs L Ms as_ → ArithmeticThetaArbitraryFourCharacterR0214.pullAlpha R W G S Ws Gs ι b hb a = as_)) := by
  intro R _ _ W _ G hG L hL h4 M
  refine ⟨ArbitraryAlphaNaturality.exists_unique_alpha R W G L M hG hL h4, ?_⟩
  intro S _ _ Ws _ Gs hGs Ms ι b hb
  refine ⟨ArbitraryAlphaNaturality.hodgeMap_isIso R W G S Ws Gs ι b hb, ?_⟩
  intro hx hy a as_ ha has
  exact ArbitraryAlphaNaturality.alpha_naturality R W G L M hG hL h4
    S Ws Gs hGs Ms ι b hb hx hy a as_ ha has

end ArithmeticThetaArbitraryFourCharacterR0214
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.exists_unique_alpha
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.hodgeMap_isIso
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.root_coefficient_covariance

#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.differential_weight
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.cartesian_local_chart

#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.alpha_local_naturality
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.pull_alpha_comp
#print axioms ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryAlphaNaturality.coefficient_base_change

#print axioms ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_alpha_naturality
