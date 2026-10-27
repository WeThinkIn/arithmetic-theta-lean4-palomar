import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaGeneralDPlusR0242
run_cmd Lean.activateScoped `ArithmeticThetaHadamard
run_cmd Lean.activateScoped `ArithmeticThetaRank16
run_cmd Lean.activateScoped `Int
run_cmd Lean.activateScoped `PowerSeries
run_cmd Lean.activateScoped `v

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ n : ℕ, 8 ∣ n → (∀ m : ℕ, ∃ e : ArithmeticThetaGeneralDPlusR0242.OriginalShell n m ≃ ArithmeticThetaRank16.NormShell n (8 * m), ∀ v, ArithmeticThetaRank16.doubledRealization n (e v).val = v.val) ∧ ArithmeticThetaGeneralDPlusR0242.originalTheta n = ArithmeticThetaRank16.theta n ∧ ArithmeticThetaComputed.theta (ArithmeticThetaRank16.latticeGram n) = PowerSeries.map (Int.castRingHom ℂ) (ArithmeticThetaGeneralDPlusR0242.originalTheta n) ∧ (0 < n → (2 : PowerSeries ℤ) * PowerSeries.expand 8 (by decide) (ArithmeticThetaGeneralDPlusR0242.originalTheta n) = ArithmeticThetaHadamard.a ^ n + ArithmeticThetaHadamard.b ^ n + ArithmeticThetaHadamard.c ^ n)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization
