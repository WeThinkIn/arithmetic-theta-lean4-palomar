module
public import ActualCategoricalRootFiberR0208
@[expose] public section

#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.object_classifier
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluation_classifier
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.fiber_triangle
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootPoint
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.pullComparison
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluationIso
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluationHomEquiv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.RootArrow
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrow
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrowInv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrow_left_inv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrow_right_inv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrowEquiv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.rootArrow_line
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.Geo
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.Geo.lift
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.Geo.compatible
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.Geo.lift_injective
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.geoOfLift
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toGeo
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.fromGeo
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.from_to
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.to_from
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.space
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toLevel
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toTest
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.geoPoint
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.geoPoint_lift
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.geoPoint_bijective
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.fiberDiscrete
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.objectEquiv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.equivalence
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.lineComponent
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluationIso_line
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.evaluationHomEquiv_line
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.underlying
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.underlying_naturality
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.lineComponent_hom
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.lineComponent_natural
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.lineComponent_iso_natural
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toGeo_line
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toGeo_inv
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.toGeo_pull
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.equivalence_obj
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.equivalence_natural_obj
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.discreteNatIso
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.equivalence_natural
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.presentation
#print axioms ArithmeticThetaActualLevelR0208.ActualCategoricalRootFiberProof.usesFiber
#print axioms ArithmeticThetaActualLevelR0208.actual_categorical_root_fiber

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaActualLevelR0208 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaMetaplecticStackR0207
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
example
    (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
    (P : Provider k L) (C : Coherence L (Base k))
    (Y : Over (Base k)) (p : Y ⟶ base P)
    (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
    (j : AnchoredMap C Y (object P p H))
    (Z : Over (Base k)) (b : Z ⟶ base P)
    (R : SquareLine Z.left ((Scheme.Modules.pullback b.left).obj (hodge P)))
    (r : AnchoredMap C Z (object P b R))
    (F : Fiber p.left H (⟨b.left,R⟩ : RootObject (base P).left (hodge P) Z.left))
    (hF : Represents F) : ∃ G : FiberPresentation j.map r.map, UsesFiber F G :=
  actual_categorical_root_fiber k L hL heven P C Y p H j Z b R r F hF
