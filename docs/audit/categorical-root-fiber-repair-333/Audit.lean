module
public import CategoricalRootFiberR0199
@[expose] public section

#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.Geo
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.Geo.lift
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.compatible_iff
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.Geo.compatible
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.Geo.lift_injective
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.toGeo
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.fromGeo
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.from_to
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.to_from
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.space
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.toLevel
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.toTest
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.geoPoint
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.geoPoint_lift
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.geoPoint_bijective
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.pointsDiscrete
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.fiberDiscrete
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.discreteEquivalence
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.component_iso_natural
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.toGeo_inv
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.toGeo_pull
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.pointEquiv
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.objectEquiv
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.equivalence
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.equivalence_obj
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.equivalence_natural_obj
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.presentation
#print axioms ArithmeticThetaStackLevelR0199.CategoricalRootFiberR0199.usesFiber
#print axioms ArithmeticThetaStackLevelR0199.categorical_root_fiber

open ArithmeticThetaStackLevelR0199
example
    (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (P : ArithmeticThetaRootStackR0198.Presentation B W)
    (Y : CategoryTheory.Over B)
    (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left
      ((AlgebraicGeometry.Scheme.Modules.pullback Y.hom).obj W))
    (T : CategoryTheory.Over B)
    (R : ArithmeticThetaSquareLinesR0192.SquareLine T.left
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj W))
    (j : ClassifiedMap P Y H) (r : ClassifiedMap P T R)
    (F : ArithmeticThetaMetaplecticTestsR0196.Fiber Y.hom H
      (⟨T.hom, R⟩ : ArithmeticThetaMetaplecticTestsR0196.RootObject B W T.left))
    (hF : ArithmeticThetaMetaplecticTestsR0196.Represents F) :
    ∃ G : FiberPresentation j.map r.map, UsesFiber j r F G :=
  categorical_root_fiber B W P Y H T R j r F hF
