module
public import TautologicalSquarePullbackR0199
@[expose] public section

#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.pointId
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.rootArrow
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.pullComparison
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.component
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.underlying
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.underlying_naturality
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.yonedaHom
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.yonedaHom_natural
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.component_hom
#print axioms ArithmeticThetaStackLevelR0199.TautologicalSquarePullbackR0199.component_natural
#print axioms ArithmeticThetaStackLevelR0199.tautological_square_pullback

example (B : AlgebraicGeometry.Scheme.{0}) (W : B.Modules)
    (P : ArithmeticThetaRootStackR0198.Presentation B W)
    (Y : CategoryTheory.Over B)
    (H : ArithmeticThetaSquareLinesR0192.SquareLine Y.left
      ((AlgebraicGeometry.Scheme.Modules.pullback Y.hom).obj W))
    (j : ArithmeticThetaStackLevelR0199.ClassifiedMap P Y H) :
    Nonempty (ArithmeticThetaStackLevelR0199.TautologicalComparison j) :=
  ArithmeticThetaStackLevelR0199.tautological_square_pullback B W P Y H j
