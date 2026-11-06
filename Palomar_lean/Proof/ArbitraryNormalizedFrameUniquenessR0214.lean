module

public import RelativeNormalizedDifferentialR0190
public import Theorems.Thm_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR

@[expose] public section

/-! Uniqueness of the normalized relative differential over arbitrary rational algebras. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryNormalizedFrameUniqueness
open CategoryTheory AlgebraicGeometry MvPolynomial
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaLegendreComparisonR0177

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)

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

private def scalar (r : R) : Γ(Curve R W, ⊤) :=
  (structureMap R W).constToPresheaf.app (Opposite.op ⊤) r

private lemma scalar_surjective : Function.Surjective (scalar R W) := by
  have hf := P2MW.S_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR.WeierstrassProjModel.K1bReduce.bijective_appTop_projModelStrCR W.toProjective
  exact hf.2.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2

private lemma scalar_restrict (r : R) :
    (Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op (scalar R W r) =
      zSection R W (chartScalar R W r) := by
  have h := CategoryTheory.congr_fun ((structureMap R W).constToPresheaf.naturality
    (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op) r
  have he : (Curve R W).presheaf.map (homOfLE (show zOpen R W ≤ ⊤ from le_top)).op (scalar R W r) =
      (structureMap R W).constToPresheaf.app (Opposite.op (zOpen R W)) r := h.symm
  rw [he]
  letI : Algebra R (ChartRing R W) := (chartScalar R W).toAlgebra
  letI := (structureMap R W).sectionsAlgebra (zOpen R W)
  apply (chartRingEquiv (chartInclusion R W)).injective
  rw [RingEquiv.apply_symm_apply]
  exact chartRingEquiv_algebraMap (structureMap R W) (chartInclusion R W) (chart_structure R W) r

/-- Equality after multiplying by the prescribed tangent coefficient follows
from normalization and faithful transport along the actual affine open immersion. -/
private lemma weighted_equal (δ δ' : CurveFrame R W)
    (hδ : NormalizedFrame R W δ) (hδ' : NormalizedFrame R W δ') :
    zSection R W (zP R W) • res (structureMap R W).kaehler
        (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ') =
      zSection R W (zP R W) • res (structureMap R W).kaehler
        (show zOpen R W ≤ ⊤ from le_top) (differentialSection R W δ) := by
  let j := chartInclusion R W
  let U := zOpen R W
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
  apply differential_on_isomorphic_sections R (structureMap R W) j U hU hV hj
  apply res_injective_of_top (j ≫ structureMap R W).kaehler _ h
  rw [differential_restrict_smul, differential_restrict_smul, chart_app_section]
  exact hδ'.symm.trans hδ

private lemma frames_equal [Algebra ℚ R] [W.IsElliptic] (δ δ' : CurveFrame R W)
    (hδ : NormalizedFrame R W δ) (hδ' : NormalizedFrame R W δ') : δ' = δ := by
  let U := zOpen R W
  let s := differentialSection R W δ
  let t := differentialSection R W δ'
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
    have hm := weighted_equal R W δ δ' hδ hδ'
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
  apply Iso.ext
  apply ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unit_hom_ext
  exact hts

end ArbitraryNormalizedFrameUniqueness

/-- The specified normalization determines the full sheaf isomorphism over
any rational algebra, including nonreduced and zero rings. -/
theorem arbitrary_normalized_frame_uniqueness :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
      (δ δ' : ArithmeticThetaGlobalFourTorsionR0190.CurveFrame R W),
      ArithmeticThetaGlobalFourTorsionR0190.NormalizedFrame R W δ →
      ArithmeticThetaGlobalFourTorsionR0190.NormalizedFrame R W δ' → δ' = δ := by
  intro R _ _ W _ δ δ' hδ hδ'
  exact ArbitraryNormalizedFrameUniqueness.frames_equal R W δ δ' hδ hδ'

end ArithmeticThetaArbitraryFourCharacterR0214

#print axioms ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_normalized_frame_uniqueness
