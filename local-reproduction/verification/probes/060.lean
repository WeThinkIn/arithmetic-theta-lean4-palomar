import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.shifted_integer_interval)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (c R : ℚ) (z : ℤ), z ∈ ArithmeticThetaLDLEnumerationR0229.shiftedInterval c R ↔ ((z : ℚ) - c)^2 ≤ R))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.shifted_integer_interval
