import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaCommonHalfHodgeR0185
run_cmd Lean.activateScoped `ArithmeticThetaComponentDegreeR0184
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaTensorPower
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaCommonHalfHodgeR0185.discriminant_twist_unit)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∃ W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H, ArithmeticThetaCommonHalfHodgeR0185.IsTwist k L D X x s W))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaCommonHalfHodgeR0185.discriminant_twist_unit
