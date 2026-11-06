import RelativeNormalizedDifferentialR0190
import Theorems.Thm_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRationalTateR0247
namespace RationalNormalizedFrame
open CategoryTheory AlgebraicGeometry MvPolynomial
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)

lemma global_functions : Function.Bijective (structureMap R W).appTop :=
  P2MW.S_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR.WeierstrassProjModel.K1bReduce.bijective_appTop_projModelStrCR W.toProjective

lemma quotient_scalar_injective : Function.Injective (algebraMap R (AffineQuotient R W)) := by
  have he (a : R) : affineQuotientEquiv R W (algebraMap R W.toAffine.CoordinateRing a) =
      algebraMap R (AffineQuotient R W) a := by
    change affineQuotientEquiv R W (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk _ (C a)
    simp [affineQuotientEquiv, ProjectiveCubicChart.polynomialEquiv, ProjectiveCubicChart.toMv]
  intro a b hab
  apply FaithfulSMul.algebraMap_injective R W.toAffine.CoordinateRing
  apply (affineQuotientEquiv R W).injective
  simpa only [he] using hab

lemma derivation_cancel {A : Type u} [CommRing A] [Algebra R A]
    (D : Derivation R A A) (p q b c : A) (h2 : IsUnit (2 : A))
    (hD : D p = 2*q + b*p) (hc : D c = 0) (hpq : IsCoprime p q)
    (hp : p*c = 0) : c = 0 := by
  have hd := congrArg D hp
  rw [Derivation.leibniz, hc, smul_zero, zero_add, hD, map_zero] at hd
  change c * (2*q+b*p) = 0 at hd
  have hq : q*c = 0 := by
    apply h2.mul_right_injective
    calc
      2*(q*c) = c*(2*q+b*p)-b*(p*c) := by ring
      _ = 2*0 := by rw [hd,hp]; ring
  obtain ⟨s,t,hst⟩ := hpq
  calc
    c = (s*p+t*q)*c := by rw [hst,one_mul]
    _ = 0 := by rw [add_mul,mul_assoc,mul_assoc,hp,hq]; simp

lemma affine_pq_coprime [W.IsElliptic] :
    IsCoprime (affineQ R W (affinePolyP R W)) (affineQ R W (affinePolyQ R W)) := by
  simpa only [affinePolyP,affinePolyQ,map_add,map_sub,map_mul,map_pow,map_ofNat,
    show ∀ b, affineQ R W (C b) = algebraMap R (AffineQuotient R W) b from fun _ => rfl] using
    affine_coefficients_coprime R W _ _ (affine_relation R W)

lemma scalar_detected [Algebra ℚ R] [W.IsElliptic] (a : R)
    (ha : affineQ R W (affinePolyP R W) * algebraMap R (AffineQuotient R W) a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AffineQuotient R W) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map
      ((algebraMap R (AffineQuotient R W)).comp (algebraMap ℚ R))
  have hz := derivation_cancel R (affineTangent R W) _ _ _ _ h2
    (affineTangent_p R W) ((affineTangent R W).map_algebraMap a)
    (affine_pq_coprime R W) ha
  apply quotient_scalar_injective R W
  simpa only [map_zero] using hz

lemma global_scalar_surjective :
    Function.Surjective (fun a : R => (structureMap R W).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
  exact (global_functions R W).surjective.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective

lemma chart_global_scalar (a : R) :
    chartRingEquiv (chartInclusion R W)
      ((Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op
        ((structureMap R W).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
      chartScalar R W a := by
  let f := structureMap R W
  let j := chartInclusion R W
  letI : Algebra R (ChartRing R W) := (chartScalar R W).toAlgebra
  letI := f.sectionsAlgebra (zOpen R W)
  have he : (Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      algebraMap R Γ(Curve R W, zOpen R W) a := by
    change (f.appTop ≫ (Curve R W).presheaf.map (homOfLE le_top).op)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = _
    rw [show f.appTop = f.appLE ⊤ ⊤ le_top by simp [Scheme.Hom.appLE, Scheme.Hom.appTop],
      Scheme.Hom.appLE_map]
    rfl
  rw [he]
  exact chartRingEquiv_algebraMap f j (chart_structure R W) a

lemma chart_scalar_detected [Algebra ℚ R] [W.IsElliptic] (a : R)
    (ha : zP R W * chartScalar R W a = 0) : a = 0 := by
  obtain ⟨e,he,hx,hy⟩ := exists_chart_equiv R W
  apply scalar_detected R W a
  have hh := congrArg e ha
  simpa only [zP,map_mul,map_add,map_ofNat,map_zero,he,hx,hy,
    affinePolyP,show ∀ b, affineQ R W (C b) = algebraMap R (AffineQuotient R W) b from fun _ => rfl] using hh

lemma normalized_frames_equal [Algebra ℚ R] [W.IsElliptic]
    (δ δ' : CurveFrame R W) (hδ : NormalizedFrame R W δ)
    (hδ' : NormalizedFrame R W δ') : δ' = δ := by
  let j := chartInclusion R W
  let U := zOpen R W
  let f := structureMap R W
  have hpre : j ⁻¹ᵁ U = ⊤ := Scheme.Hom.preimage_image_eq j ⊤
  have h : ⊤ ≤ j ⁻¹ᵁ U := hpre.ge
  have hU : IsAffineOpen U := by
    change IsAffineOpen (j ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange j
  have hV : IsAffineOpen (j ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  have hj : Function.Bijective (j.app U) := by
    haveI : IsIso (j.app U) := j.isIso_app U (by
      change j ''ᵁ ⊤ ≤ j.opensRange
      rw [Scheme.Hom.image_top_eq_opensRange])
    exact ConcreteCategory.bijective_of_isIso _
  have hm : zSection R W (zP R W) • res f.kaehler (show U ≤ ⊤ from le_top) (differentialSection R W δ') =
      zSection R W (zP R W) • res f.kaehler (show U ≤ ⊤ from le_top) (differentialSection R W δ) := by
    apply differential_on_isomorphic_sections R f j U hU hV hj
    apply res_injective_of_top (j ≫ f).kaehler _ h
    rw [differential_restrict_smul, differential_restrict_smul, chart_app_section]
    exact hδ'.symm.trans hδ
  let c : Γ(Curve R W, ⊤) := Scheme.Modules.Hom.app δ.inv ⊤ (differentialSection R W δ')
  obtain ⟨a,ha⟩ := global_scalar_surjective R W c
  have hid : Scheme.Modules.Hom.app δ.inv ⊤ (differentialSection R W δ) = (1 : Γ(Curve R W,⊤)) := by
    change Scheme.Modules.Hom.app δ.inv ⊤ (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve R W,⊤))) = _
    exact congrArg (fun k : (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules) ⟶
      (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules) =>
        Scheme.Modules.Hom.app k ⊤ (1 : Γ(Curve R W,⊤))) δ.hom_inv_id
  have hh := congrArg (Scheme.Modules.Hom.app δ.inv U) hm
  rw [Scheme.Modules.Hom.app_smul,Scheme.Modules.Hom.app_smul] at hh
  rw [← hom_res, ← hom_res, hid] at hh
  change zSection R W (zP R W) * (Curve R W).presheaf.map (homOfLE le_top).op c =
    zSection R W (zP R W) * (Curve R W).presheaf.map (homOfLE le_top).op 1 at hh
  rw [map_one, ← ha] at hh
  have hh' := congrArg (chartRingEquiv j) hh
  simp only [j,map_mul,map_one,RelativeNormalizedDifferential.zSection,RingEquiv.apply_symm_apply] at hh'
  change zP R W * chartRingEquiv j ((Curve R W).presheaf.map (homOfLE le_top).op
    ((structureMap R W).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) = zP R W * 1 at hh'
  rw [chart_global_scalar] at hh'
  have ha1 : a = 1 := by
    have hz : zP R W * chartScalar R W (a-1) = 0 := by
      rw [map_sub,map_one,mul_sub,hh',sub_self]
    exact sub_eq_zero.mp (chart_scalar_detected R W (a-1) hz)
  have hc : c = 1 := by simpa only [ha1,map_one] using ha.symm
  apply Iso.ext
  apply ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unit_hom_ext
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app δ.inv ⊤)).injective
  exact hc.trans hid.symm

end RationalNormalizedFrame
open ArithmeticThetaGlobalFourTorsionR0190

theorem rational_normalized_frame :
    ∀ (R : Type) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic],
      ∃! δ : CurveFrame R W, NormalizedFrame R W δ := by
  intro R _ _ W _
  obtain ⟨δ,hδ⟩ := RelativeNormalizedDifferential.normalized_frame_exists R W
  exact ⟨δ,hδ,fun δ' hδ' => RationalNormalizedFrame.normalized_frames_equal R W δ δ' hδ hδ'⟩

#print axioms rational_normalized_frame
end ArithmeticThetaRationalTateR0247
