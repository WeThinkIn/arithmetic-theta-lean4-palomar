import OrderedLegendreParameterRigidityR0177
import Mathlib.RingTheory.LocalProperties.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202
open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaLegendreComparisonR0177.OrderedLegendreParameterRigidity

/-- Ordered marked Legendre parameters agree over arbitrary rational affine bases.
Equality is tested in localizations, so no reducedness hypothesis is needed. -/
theorem arbitrary_ordered_parameter :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (lam mu : R), IsUnit (lam * (lam - 1)) → IsUnit (mu * (mu - 1)) → ∀ (p0 p1 : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam))) (q0 q1 : Quiver.Hom (ArithmeticThetaRelativeDiscriminantR0171.Base R) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu))), ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p0 0 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) p1 1 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) q0 0 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) q1 1 0 → ∀ f : CategoryTheory.Iso (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) (ArithmeticThetaRelativeKatoR0169.Curve R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu)), CategoryTheory.CategoryStruct.comp (f.hom) (ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu)) = ArithmeticThetaRelativeKatoR0169.structureMap R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam) → CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R lam)) (f.hom) = ArithmeticThetaRelativeKatoR0169.origin R (ArithmeticThetaLegendreComparisonR0177.legendreAt R mu) → CategoryTheory.CategoryStruct.comp (p0) (f.hom) = q0 → CategoryTheory.CategoryStruct.comp (p1) (f.hom) = q1 → lam = mu := by
  intro R _ _ lam mu _hlam _hmu p0 p1 q0 q1 hp0 hp1 hq0 hq1 f hf ho h0 h1
  apply Module.eq_of_localization_maximal
    (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap R (Localization.AtPrime P))
  intro P hP
  let K := Localization.AtPrime P
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
  exact h

#print axioms arbitrary_ordered_parameter
end ArithmeticThetaArbitraryAffineR0202
