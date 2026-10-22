module

public import NormalAffineClassifyingConstructionR0178
public import CompatibleLevelDefinitionsR0178

@[expose] public section

/-! New output data for classification over arbitrary affine rational bases.
No domain, reducedness, noetherianity or normality is required of the test ring
or the quadratic cover. Every map and identity is construction output.
The existing Classifies predicate is reused without changing its semantics. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryAffineR0202
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaCompatibleLevelR0178

/-- Full normalized presentation on a degree-two finite etale cover. -/
structure NormalForm (k R : Type u) [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra ℚ R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G 2 (𝟙 (Base R))) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  inclusion : R →ₐ[k] ring
  finite : IsFinite (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  etale : Etale (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  surjective : Surjective (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  degree : ∀ z, (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z = 2
  roots : Fin 3 → R
  coordinates : TwoCoordinates R W G M roots
  parameter : R
  parameter_unit : IsUnit (parameter * (parameter - 1))
  parameter_eq : parameter * (roots 1 - roots 0) = roots 2 - roots 0
  scaling : ringˣ
  scaling_eq : (scaling : ring)^2 = inclusion (roots 1 - roots 0)
  parameterMap : LegendreRing k →ₐ[k] ring
  parameterMap_eq : parameterMap (ArithmeticThetaLegendreAtlasR0176.parameter k) =
    inclusion parameter
  map : Curve ring ((legendre k).map parameterMap.toRingHom) ⟶ Curve R W
  cartesian : IsPullback map
    (structureMap ring ((legendre k).map parameterMap.toRingHom)) (structureMap R W)
    (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  origin_eq : origin ring ((legendre k).map parameterMap.toRingHom) ≫ map =
    Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ origin R W
  affineMap : ChartRing R W →+* ChartRing ring ((legendre k).map parameterMap.toRingHom)
  affine_eq : Spec.map (CommRingCat.ofHom affineMap) ≫ chartInclusion R W =
    chartInclusion ring ((legendre k).map parameterMap.toRingHom) ≫ map
  x_eq : affineMap (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) =
    chartScalar ring ((legendre k).map parameterMap.toRingHom) ((scaling : ring)^2) *
      WeierstrassCurve.DrinfeldGlobal.xOverZ ((legendre k).map parameterMap.toRingHom).toProjective +
    chartScalar ring ((legendre k).map parameterMap.toRingHom) (inclusion (roots 0))
  y_eq : affineMap (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) =
    chartScalar ring ((legendre k).map parameterMap.toRingHom) ((scaling : ring)^3) *
      WeierstrassCurve.DrinfeldGlobal.yOverZ ((legendre k).map parameterMap.toRingHom).toProjective -
    chartScalar ring ((legendre k).map parameterMap.toRingHom) (inclusion (algebraMap ℚ R (1/2))) *
      (chartScalar ring ((legendre k).map parameterMap.toRingHom) (inclusion W.a₁) *
        affineMap (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) +
        chartScalar ring ((legendre k).map parameterMap.toRingHom) (inclusion W.a₃))
  point0 : Base ring ⟶ Curve ring ((legendre k).map parameterMap.toRingHom)
  point1 : Base ring ⟶ Curve ring ((legendre k).map parameterMap.toRingHom)
  point0_coordinates : HasCoordinates ring ((legendre k).map parameterMap.toRingHom) point0 0 0
  point1_coordinates : HasCoordinates ring ((legendre k).map parameterMap.toRingHom) point1 1 0
  point0_eq : point0 ≫ map = Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ M.x.val
  point1_eq : point1 ≫ map = Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ M.y.val
attribute [instance] NormalForm.commRing NormalForm.algebra

/-- Local coverage by the ACCEPTED parameter family. Both labels and the origin
are preserved through a Cartesian comparison; no fine-moduli conclusion is
encoded here. A degree-two finite etale cover is constructed; its ring may be disconnected or nonreduced. -/
structure AtlasComparison (k R : Type u) [Field k] [CharZero k] [CommRing R]
    [Algebra k R] (W : WeierstrassCurve R) (G : Law R W) {L : ℕ}
    (M : FullLevel R W G L (𝟙 (Base R))) (A : LegendreAtlas k L) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  inclusion : R →ₐ[k] ring
  finite : IsFinite (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  etale : Etale (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  surjective : Surjective (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  degree : ∀ z, (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z = 2
  sourceMap : Curve ring (W.map inclusion.toRingHom) ⟶ Curve R W
  sourceCartesian : IsPullback sourceMap (structureMap ring (W.map inclusion.toRingHom))
    (structureMap R W) (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  sourceOrigin : origin ring (W.map inclusion.toRingHom) ≫ sourceMap =
    Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ origin R W
  x : Base ring ⟶ Curve ring (W.map inclusion.toRingHom)
  y : Base ring ⟶ Curve ring (W.map inclusion.toRingHom)
  x_over : x ≫ structureMap ring (W.map inclusion.toRingHom) = 𝟙 _
  y_over : y ≫ structureMap ring (W.map inclusion.toRingHom) = 𝟙 _
  x_lift : x ≫ sourceMap = Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ M.x.val
  y_lift : y ≫ sourceMap = Spec.map (CommRingCat.ofHom inclusion.toRingHom) ≫ M.y.val
  base : Base ring ⟶ Base A.quotient.ring
  base_over : base ≫ Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k ring))
  comparison : Curve ring (W.map inclusion.toRingHom) ⟶ A.descent.family.curve
  cartesian : IsPullback comparison (structureMap ring (W.map inclusion.toRingHom))
    A.descent.family.projection base
  origin_eq : origin ring (W.map inclusion.toRingHom) ≫ comparison =
    base ≫ (A.descent.family.law.one (𝟙 _)).val
  x_eq : x ≫ comparison = base ≫ A.marking.x.val
  y_eq : y ≫ comparison = base ≫ A.marking.y.val
attribute [instance] AtlasComparison.commRing AtlasComparison.algebra


variable (k : Type u) [Field k] [CharZero k] (L : ℕ) (A : LegendreAtlas k L)

structure LocalComparison (B : TwoMarking k L A) (C : CompatibleCover k L A B)
    (Q : CompatibleQuotient k L A B C)
    (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G L (𝟙 (Base R))) where
  comparison : AtlasComparison k R W G M A
  base : Base comparison.ring ⟶ Base Q.quotient.ring
  factorization : base ≫ Q.inclusion = comparison.base
  over_eq : base ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k comparison.ring))


end ArithmeticThetaArbitraryAffineR0202
