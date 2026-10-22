module

public import ArbitraryDiscriminantDefinitionsR0243
public import Definitions.Def_WeierstrassCurve_Generic
public import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
public import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
public import Mathlib.Algebra.Field.ULift

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryDiscriminantR0243
namespace NormalModelConstruction
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

abbrev Coefficients := MvPolynomial (Fin 5) (ULift.{u} ℚ)
abbrev universalPolynomial : WeierstrassCurve Coefficients.{u} :=
  WeierstrassCurve.Generic.poly (ULift.{u} ℚ)
abbrev Source := Localization.Away universalPolynomial.{u}.Δ

instance sourceDomain : IsDomain Source.{u} :=
  IsLocalization.Away.isDomain Source.{u}
    (WeierstrassCurve.Generic.Δ_poly_ne_zero (ULift.{u} ℚ))

def equation : WeierstrassCurve Source.{u} :=
  universalPolynomial.{u}.map (algebraMap Coefficients.{u} Source.{u})

instance equationElliptic : equation.{u}.IsElliptic := by
  constructor
  rw [equation, WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit _

def evaluate {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) :
    Coefficients.{u} →+* R :=
  MvPolynomial.eval₂Hom ((algebraMap ℚ R).comp ULift.ringEquiv.toRingHom)
    (WeierstrassCurve.Generic.coeffs W)

lemma polynomial_map_evaluate {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) : universalPolynomial.map (evaluate W) = W := by
  cases W
  simp [evaluate, WeierstrassCurve.Generic.poly, WeierstrassCurve.map,
    WeierstrassCurve.Generic.coeffs]

lemma evaluate_discriminant_unit {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    IsUnit (evaluate W universalPolynomial.{u}.Δ) := by
  rw [← WeierstrassCurve.map_Δ, polynomial_map_evaluate]
  exact W.isUnit_Δ

def scalar {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    [W.IsElliptic] : Source.{u} →ₐ[ℚ] R :=
  let f : Source.{u} →+* R := IsLocalization.Away.lift
    (R := Coefficients.{u}) (S := Source.{u}) (g := evaluate W)
    universalPolynomial.{u}.Δ (evaluate_discriminant_unit W)
  { f with commutes' := f.map_rat_algebraMap }

lemma equation_map_scalar {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] : equation.map (scalar W).toRingHom = W := by
  have hc : (scalar W).toRingHom.comp (algebraMap Coefficients.{u} Source.{u}) =
      evaluate W := IsLocalization.Away.lift_comp (S := Source.{u})
        universalPolynomial.{u}.Δ (evaluate_discriminant_unit W)
  rw [equation, WeierstrassCurve.map_map, hc]
  exact polynomial_map_evaluate W

lemma origin_law : ∃ G : Law Source.{u} equation.{u}, IsOriginLaw Source equation G := by
  obtain ⟨G, hc, ho⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_isCommutative_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
      equation.{u}.toProjective
      (WeierstrassProjModel.projModel_pullback_iso_baseChange equation.{u}.toProjective)
  exact ⟨G, ho, hc⟩

lemma pointed_comparison {R : Type u} [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law Source.{u} equation.{u}) (hG : IsOriginLaw Source equation G) :
    Nonempty (Comparison Source R equation W (scalar W).toRingHom) := by
  obtain ⟨H, hH, b, hb, he, hn⟩ :=
    ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.weierstrass_base_change
      equation G hG (scalar W).toRingHom
  have hC : Nonempty (Comparison Source R equation
      (equation.map (scalar W).toRingHom) (scalar W).toRingHom) :=
    ⟨⟨b, hb, he⟩⟩
  simpa only [equation_map_scalar] using hC

end NormalModelConstruction

theorem normal_discriminant_model :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic],
      Nonempty (NormalModel R W) := by
  intro R _ _ W _
  let A := NormalModelConstruction.Source.{u}
  let V := NormalModelConstruction.equation.{u}
  obtain ⟨G, hG⟩ := NormalModelConstruction.origin_law.{u}
  obtain ⟨C⟩ := NormalModelConstruction.pointed_comparison W G hG
  have hg := ArithmeticThetaRelativeKatoR0169.relative_curve_geometry A V
  exact ⟨{
    ring := A
    equation := V
    integral := hg.1
    locallyNoetherian := hg.2.1
    genericIntegral := hg.2.2.2.1
    genericLocallyNoetherian := hg.2.2.2.2.1
    law := G
    originLaw := hG
    scalar := NormalModelConstruction.scalar W
    comparison := C
  }⟩

#print axioms normal_discriminant_model
end ArithmeticThetaArbitraryDiscriminantR0243
