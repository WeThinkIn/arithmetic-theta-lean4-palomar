module
public import ActualAnchoredPullbackR0208
@[expose] public section

#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.pointId
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.component
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.yonedaHom
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.component_hom
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.yonedaHom_natural
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.component_natural
#print axioms ArithmeticThetaActualLevelR0208.ActualAnchoredPullbackProof.component_identity
#print axioms ArithmeticThetaActualLevelR0208.actual_anchored_pullback

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaActualLevelR0208 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaMetaplecticStackR0207
example
    (k : Type) [Field k] [CharZero k] (L : ℕ)
    (C : Coherence L (Base k)) (Y : Over (Base k))
    (X : (group L Y.left).Objects) (j : AnchoredMap C Y X) :
    Nonempty (PullbackComparison j) :=
  actual_anchored_pullback k L C Y X j
