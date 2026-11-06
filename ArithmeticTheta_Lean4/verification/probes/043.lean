import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaGlobalFourTorsionR0190
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `Opposite

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGlobalFourTorsionR0190.compact_full_level_alpha)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∃! a : (H.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.IsOpenAlpha L k D (ArithmeticThetaGlobalFourTorsionR0190.restrictAlpha L k D X H a) ∧ ArithmeticThetaGlobalFourTorsionR0190.CuspOrders L k D X H a ∧ ArithmeticThetaGlobalFourTorsionR0190.ExactTateAlpha L k D X H a))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGlobalFourTorsionR0190.compact_full_level_alpha
