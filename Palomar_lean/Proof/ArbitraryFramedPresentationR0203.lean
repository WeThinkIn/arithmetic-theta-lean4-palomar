module

public import FramedFiniteTypeApproximationR0203
public import NoetherianFramedPresentationR0203
public import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom

@[expose] public section

/-! Pointed Weierstrass presentations over arbitrary rational rings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- Descend to a finite-type rational base, present there, and compare the two
actual Cartesian squares after coefficient change. Translation by a section
then identifies the original identity with the standard Weierstrass origin. -/
theorem arbitrary_framed_presentation
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (W : WeierstrassCurve R) (hW : W.IsElliptic)
      (e : CategoryTheory.Iso Q.target (ArithmeticThetaRelativeKatoR0169.Curve R W)),
      e.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W = Q.structureMap ∧
      Q.zero ≫ e.hom = ArithmeticThetaRelativeKatoR0169.origin R W := by
  obtain ⟨D⟩ := framed_finite_type_approximation R Q
  letI := D.commRing
  letI := D.rational
  letI := D.finiteType
  letI : IsNoetherianRing D.ring := Algebra.FiniteType.isNoetherianRing ℚ D.ring
  obtain ⟨W, hW, e, he, _⟩ := noetherian_framed_presentation D.ring D.model
  letI := hW
  let W' : WeierstrassCurve R := W.map D.scalar.toRingHom
  obtain ⟨φ, hφ, hcoef⟩ :=
    WeierstrassProjModel.exists_isCoefficientHom W.toProjective D.scalar.toRingHom
  have sqW := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
    W.toProjective D.scalar.toRingHom φ hφ hcoef
  have sqe : IsPullback e.hom D.model.structureMap
      (ArithmeticThetaRelativeKatoR0169.structureMap D.ring W) (𝟙 (Base D.ring)) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  have sqQ : IsPullback (D.comparison ≫ e.hom) Q.structureMap
      (ArithmeticThetaRelativeKatoR0169.structureMap D.ring W)
      (Spec.map (CommRingCat.ofHom D.scalar.toRingHom)) := by
    simpa only [Category.comp_id] using D.cartesian.paste_horiz sqe
  let e' : Q.target ≅ ArithmeticThetaRelativeKatoR0169.Curve R W' :=
    sqQ.isoIsPullback _ _ sqW
  have he' : e'.hom ≫ ArithmeticThetaRelativeKatoR0169.structureMap R W' =
      Q.structureMap := sqQ.isoIsPullback_hom_snd _ _ sqW
  obtain ⟨e'', he'', hz⟩ :=
    ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PointedIso.adjust_identity
      Q.law e' he' (WeierstrassProjModel.kwZeroSect R W').val
      (WeierstrassProjModel.kwZeroSect R W').property
  exact ⟨W', inferInstance, e'', he'', hz⟩

#print axioms arbitrary_framed_presentation

end ArithmeticThetaLocalWeierstrassR0203
