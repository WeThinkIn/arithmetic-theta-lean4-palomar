import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaFormalConstants
run_cmd Lean.activateScoped `ArithmeticThetaFormalCoverR0210
run_cmd Lean.activateScoped `C
run_cmd Lean.activateScoped `CommRingCat
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaFormalCoverR0210.arbitrary_formal_cover_constant)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))) [CharZero k] [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Smooth (ArithmeticThetaFormalConstants.genericStructure k X f)] [AlgebraicGeometry.GeometricallyConnected (ArithmeticThetaFormalConstants.genericStructure k X f)], ∃ ρ : ArithmeticThetaFormalCoverR0210.Restrictions k X f, ∀ C : ArithmeticThetaFormalCoverR0210.Cover k X f, ArithmeticThetaFormalCoverR0210.ChartConditions k X f C → ∀ v : (∀ i, ArithmeticThetaFormalCoverR0210.Fractions k X f (C.opens i)), ArithmeticThetaFormalCoverR0210.RationalCompatible k X f ρ C v → ArithmeticThetaFormalCoverR0210.NoPole k X f C v → ∃! c : LaurentSeries k, ArithmeticThetaFormalCoverR0210.FractionConstant k X f C v c))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaFormalCoverR0210.arbitrary_formal_cover_constant
