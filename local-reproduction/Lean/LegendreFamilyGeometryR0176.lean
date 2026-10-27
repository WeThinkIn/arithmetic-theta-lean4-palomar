import LegendreLevelAtlasDefinitionsR0176
import RelativeCurveGeometryR0169
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists
import Theorems.Thm_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Geometry of the universal Legendre family on the complement of 0 and 1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

namespace LegendreFamilyGeometryR0176

variable (k : Type u) [Field k] [CharZero k]

private lemma denominator_ne_zero :
    (Polynomial.X * (Polynomial.X - 1) : Polynomial k) ≠ 0 := by
  exact mul_ne_zero Polynomial.X_ne_zero (by
    intro h
    have := congrArg (fun p : Polynomial k => p.coeff 1) h
    simpa [Polynomial.coeff_one] using this)

private lemma base_domain : IsDomain (LegendreRing k) :=
  Localization.Away.isDomain (denominator_ne_zero k)

private lemma base_normal : IsIntegrallyClosed (LegendreRing k) := by
  exact isIntegrallyClosed_of_isLocalization (R := Polynomial k) (LegendreRing k)
    (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
    (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr (denominator_ne_zero k)))

private lemma discriminant : (legendre k).Δ =
    16 * (parameter k * (parameter k - 1)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, legendre]
  ring

private lemma elliptic : (legendre k).IsElliptic := by
  have hu : IsUnit (parameter k * (parameter k - 1)) := by
    have h := IsLocalization.Away.algebraMap_isUnit
      (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
    rw [map_mul, map_sub, map_one] at h
    exact h
  have h16 : IsUnit (16 : LegendreRing k) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (16 : k) ≠ 0)).map
        (algebraMap k (LegendreRing k))
  exact ⟨by rw [discriminant]; exact h16.mul (hu.pow 2)⟩

private lemma base_smooth : SmoothOfRelativeDimension 1 (legendreBaseMap k) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{1} k) := by
    simpa using P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr.SplitTorusSmoothEngine.isStandardSmoothOfRelativeDimension_mvPolynomial k PUnit.{1}
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv k PUnit.{1})
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial k) (LegendreRing k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away
      (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
  have hs : Algebra.IsStandardSmoothOfRelativeDimension 1 k (LegendreRing k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 k (Polynomial k) (LegendreRing k)
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hs)

end LegendreFamilyGeometryR0176

theorem legendre_family_geometry :
    ∀ (k : Type u) [Field k] [CharZero k],
    IsDomain (LegendreRing k) ∧ IsNoetherianRing (LegendreRing k) ∧
    IsIntegrallyClosed (LegendreRing k) ∧ (legendre k).IsElliptic ∧
    SmoothOfRelativeDimension 1 (legendreBaseMap k) ∧
    ∃ G : Law (LegendreRing k) (legendre k), IsOriginLaw (LegendreRing k) (legendre k) G := by
  intro k _ _
  letI := LegendreFamilyGeometryR0176.base_domain k
  letI := LegendreFamilyGeometryR0176.base_normal k
  letI := LegendreFamilyGeometryR0176.elliptic k
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    LegendreFamilyGeometryR0176.base_smooth k, ?_⟩
  have hgeom := relative_curve_geometry (LegendreRing k) (legendre k)
  letI : SmoothOfRelativeDimension 1 (structureMap (LegendreRing k) (legendre k)) :=
    hgeom.2.2.2.2.2.1
  have htwo : IsUnit (2 : LegendreRing k) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : k) ≠ 0)).map
        (algebraMap k (LegendreRing k))
  letI : Invertible (2 : LegendreRing k) := htwo.invertible
  obtain ⟨_, _, _, G, _, hone, hcomm⟩ :=
    WeierstrassProjModel.relativeGroupLaw_exists (legendre k)
      (inferInstance : Smooth (structureMap (LegendreRing k) (legendre k)))
      hgeom.2.2.2.2.2.2 (legendre k).isUnit_Δ
  exact ⟨G, hone, hcomm⟩

end ArithmeticThetaLegendreAtlasR0176
