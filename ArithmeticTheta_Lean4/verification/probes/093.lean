import Lean
import FullSourceIntegrationR0268


set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaElementary.norm_sign_exponent_even)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (c d : ℤ), Odd c → Even ((c - 1) * (d - 1) * (1 - c * (d + 1)) / 2)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaElementary.norm_sign_exponent_even
