import FormalConstantDefinitions
import SmoothGeometricallyConnectedIntegral
import GenericFiberRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
noncomputable section
namespace ArithmeticThetaFormalConstants

lemma structuralMap_top (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) :
    structuralMap R X f ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom := by
  change ((Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ ⊤ le_top).hom = _
  congr 2
  simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

/-- The scalar square for the actual categorical generic-fiber projection. -/
theorem generic_structural_naturality (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) :
    ((pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k))))).appTop.hom).comp
      (structuralMap (PowerSeries k) X f ⊤) =
    (ArithmeticThetaProperFunctions.constantMap (LaurentSeries k)
      (genericFiber k X f) (genericStructure k X f)).comp
        (algebraMap (PowerSeries k) (LaurentSeries k)) := by
  rw [structuralMap_top]
  have hΓ := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
  have happ : f.appTop ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k))))).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))).appTop ≫
        (genericStructure k X f).appTop := by
    change (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k)))) ≫ f).appTop =
      (genericStructure k X f ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (PowerSeries k) (LaurentSeries k)))).appTop
    rw [pullback.condition]
  change ((Scheme.ΓSpecIso _).inv ≫ f.appTop ≫ _).hom =
    ((CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫
      (Scheme.ΓSpecIso _).inv ≫ (genericStructure k X f).appTop).hom
  rw [← Category.assoc, ← Category.assoc, hΓ, Category.assoc, happ]
  rfl

/-- Every global regular function is a unique structural power series. -/
theorem proper_model_global_constants :
    ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
      (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))))
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f]
      [AlgebraicGeometry.Smooth (genericStructure k X f)]
      [AlgebraicGeometry.GeometricallyConnected (genericStructure k X f)],
      Function.Bijective (structuralMap (PowerSeries k) X f ⊤) := by
  intro k _ X f _ _ _ _
  let q := (pullback.fst f (Spec.map (CommRingCat.ofHom
    (algebraMap (PowerSeries k) (LaurentSeries k))))).appTop.hom
  let c := ArithmeticThetaProperFunctions.constantMap (LaurentSeries k)
    (genericFiber k X f) (genericStructure k X f)
  haveI : GeometricallyIntegral (genericStructure k X f) :=
    ArithmeticThetaCompletedCharts.smooth_geometrically_connected_integral
      (LaurentSeries k) (genericFiber k X f) (genericStructure k X f)
  haveI : IsProper (genericStructure k X f) := by
    dsimp [genericStructure]
    infer_instance
  have hc : Function.Bijective c :=
    ArithmeticThetaConstantDescent.proper_geometrically_integral_constants_bijective
      (LaurentSeries k) (genericFiber k X f) (genericStructure k X f)
  have hq : Function.Injective q :=
    ArithmeticThetaCompletedCharts.generic_fiber_restriction_injective k X f
  have hsquare : q.comp (structuralMap (PowerSeries k) X f ⊤) =
      c.comp (algebraMap (PowerSeries k) (LaurentSeries k)) :=
    generic_structural_naturality k X f
  have hi : (structuralMap (PowerSeries k) X f ⊤).IsIntegral := by
    rw [structuralMap_top]
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  constructor
  · intro a b hab
    apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
    apply hc.injective
    have h := congrArg q hab
    simpa only [← RingHom.comp_apply, hsquare] using h
  · intro s
    obtain ⟨a, ha⟩ := hc.surjective (q s)
    have hai : IsIntegral (PowerSeries k) a := by
      apply RingHom.IsIntegralElem.of_map hc.injective
      rw [← hsquare, ha]
      exact (hi s).map q
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hai
    refine ⟨r, hq ?_⟩
    change (q.comp (structuralMap (PowerSeries k) X f ⊤)) r = q s
    rw [hsquare, RingHom.comp_apply, hr, ha]

end ArithmeticThetaFormalConstants
