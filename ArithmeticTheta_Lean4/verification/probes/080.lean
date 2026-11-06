import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaGeneralDPlusR0242

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGeneralDPlusR0242.general_dplus_dual)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ n : ℕ, 8 ∣ n → ∀ v : Fin n → ℚ, ArithmeticThetaGeneralDPlusR0242.dualMember n v ↔ v ∈ ArithmeticThetaGeneralDPlusR0242.lattice n))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_dual
