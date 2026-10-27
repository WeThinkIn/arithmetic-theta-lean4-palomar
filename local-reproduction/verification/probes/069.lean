import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAdaptiveSolverR0230
run_cmd Lean.activateScoped `ArithmeticThetaComputed

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAdaptiveSolverR0230.adaptive_singleton_zero)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A : ArithmeticThetaAdaptiveSolverR0230.Matrices n 1), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ cs : List (ArithmeticThetaAdaptiveSolverR0230.Change n 1), ArithmeticThetaAdaptiveSolverR0230.solveChanges A cs = some (ArithmeticThetaAdaptiveSolverR0230.assemble A 0) ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A (ArithmeticThetaAdaptiveSolverR0230.assemble A 0)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_singleton_zero
