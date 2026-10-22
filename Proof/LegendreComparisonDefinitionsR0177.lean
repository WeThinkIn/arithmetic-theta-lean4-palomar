module

public import LegendreLevelFamilyConstructionR0176
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import LegendreLevelAtlasDefinitionsR0176

@[expose] public section

/-! Local Legendre comparisons for actual marked projective elliptic families.
All existence data below are construction targets, not new assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176

abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective

def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective

def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom

def HasCoordinates (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (P : Base R ⟶ Curve R W) (x y : R) : Prop :=
  P ≫ structureMap R W = 𝟙 (Base R) ∧
  ∃ χ : ChartRing R W →+* R,
    P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
    χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = x ∧
    χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = y

def twoPoint (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (M : FullLevel R W G 2 (𝟙 (Base R))) (i : Fin 3) :
    Base R ⟶ Curve R W :=
  ![M.x.val, M.y.val, (G.mul (𝟙 (Base R)) M.x M.y).val] i

def TwoCoordinates (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G 2 (𝟙 (Base R))) (e : Fin 3 → R) : Prop :=
  ∀ i, HasCoordinates R W (twoPoint R W G M i) (e i)
    (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i + W.a₃))

def completedCubic (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.X^3 + Polynomial.C (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2) * Polynomial.X^2 +
    Polynomial.C (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃) * Polynomial.X +
    Polynomial.C (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)

def SplitCubic (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) (e : Fin 3 → R) : Prop :=
  (∀ i j, i ≠ j → IsUnit (e i - e j)) ∧
    completedCubic R W = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (e i))

def legendreAt (R : Type u) [CommRing R] (lam : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := -(lam + 1)
  a₃ := 0
  a₄ := lam
  a₆ := 0

/-- A degree at most two connected etale extension and a normalized Cartesian
Legendre presentation. Coordinates, parameter, and both marked points are tied
to the SAME morphism. The extension, maps and all assertions are outputs. -/
structure NormalForm (k R : Type u) [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra ℚ R] (W : WeierstrassCurve R) (G : Law R W)
    (M : FullLevel R W G 2 (𝟙 (Base R))) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [algebra : Algebra k ring]
  inclusion : R →ₐ[k] ring
  finite : IsFinite (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  etale : Etale (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  surjective : Surjective (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  degree : ∀ z, 0 < (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z ∧
    (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z ≤ 2
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
attribute [instance] NormalForm.commRing NormalForm.domain NormalForm.noetherian
  NormalForm.normal NormalForm.algebra

/-- Local coverage by the ACCEPTED parameter family. Both labels and the origin
are preserved through a Cartesian comparison; no fine-moduli conclusion is
encoded here. A normal connected degree at most two extension is constructed. -/
structure AtlasComparison (k R : Type u) [Field k] [CharZero k] [CommRing R]
    [Algebra k R] (W : WeierstrassCurve R) (G : Law R W) {L : ℕ}
    (M : FullLevel R W G L (𝟙 (Base R))) (A : LegendreAtlas k L) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [algebra : Algebra k ring]
  inclusion : R →ₐ[k] ring
  finite : IsFinite (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  etale : Etale (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  surjective : Surjective (Spec.map (CommRingCat.ofHom inclusion.toRingHom))
  degree : ∀ z, 0 < (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z ∧
    (Spec.map (CommRingCat.ofHom inclusion.toRingHom)).finrank z ≤ 2
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
attribute [instance] AtlasComparison.commRing AtlasComparison.domain AtlasComparison.noetherian
  AtlasComparison.normal AtlasComparison.algebra

end ArithmeticThetaLegendreComparisonR0177
