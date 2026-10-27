import RelativeKatoDefinitionsR0169
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk

/-! Geometry of the actual projective Weierstrass family over a normal base. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoR0169
open CategoryTheory AlgebraicGeometry

/-- The total family and its generic curve have the geometry needed for relative divisors. -/
theorem relative_curve_geometry :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic], AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W) ∧ AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W) ∧ (∀ x : (ArithmeticThetaRelativeKatoR0169.Curve R W), IsIntegrallyClosed ((ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.stalk x)) ∧ AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W) ∧ AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W) ∧ AlgebraicGeometry.SmoothOfRelativeDimension 1 (ArithmeticThetaRelativeKatoR0169.structureMap R W) ∧ AlgebraicGeometry.GeometricallyIntegral (ArithmeticThetaRelativeKatoR0169.structureMap R W) := by
  intro R _ _ _ _ _ W _
  let : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  let : GeometricallyIntegral (structureMap R W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  have hi : IsIntegral (Curve R W) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (structureMap R W)
  have hn : IsLocallyNoetherian (Curve R W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap R W)
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
    MulEquiv.isDomain R e.symm.toMulEquiv
  let : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) :=
    IsIntegrallyClosed.of_equiv e
  have hnormal : ∀ x : Curve R W,
      IsIntegrallyClosed ((Curve R W).presheaf.stalk x) := fun x =>
    (Smooth.isDomain_and_isIntegrallyClosed_stalk (structureMap R W) x).2
  let Wg := W.map (algebraMap R (FractionRing R))
  let pg := ArithmeticThetaGeneralEllipticKatoR0168.structureMap (FractionRing R) Wg
  let : SmoothOfRelativeDimension 1 pg :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one Wg.toProjective
  let : GeometricallyIntegral pg :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso Wg
      (WeierstrassProjModel.projModel_pullback_iso_baseChange Wg.toProjective)
  exact ⟨hi, hn, hnormal,
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian pg,
    LocallyOfFiniteType.isLocallyNoetherian pg, inferInstance, inferInstance⟩

end ArithmeticThetaRelativeKatoR0169
