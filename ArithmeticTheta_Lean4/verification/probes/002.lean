import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `Nat

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaElementary.rank_zero_coefficients)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ, Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaElementary.rank_zero_coefficients
