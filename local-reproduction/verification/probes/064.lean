import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaEnumeration
run_cmd Lean.activateScoped `ArithmeticThetaLDLEnumerationR0229
run_cmd Lean.activateScoped `PowerSeries
run_cmd Lean.activateScoped `a

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ArithmeticThetaComputed.validGram A → (∀ m : ℕ, ArithmeticThetaLDLEnumerationR0229.shell A m = ArithmeticThetaEnumeration.shellVectors A m) ∧ ∀ B : ℕ, ArithmeticThetaLDLEnumerationR0229.coefficients A B = ArithmeticThetaEnumeration.coefficientsUpTo A B ∧ (ArithmeticThetaLDLEnumerationR0229.coefficients A B).length = B + 1 ∧ ∀ a : Fin (B+1), ((ArithmeticThetaLDLEnumerationR0229.coefficients A B).getD a.val 0 : ℂ) = PowerSeries.coeff a.val (ArithmeticThetaComputed.theta A)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix
