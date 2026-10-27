import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAdaptiveSolverR0230
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `o

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAdaptiveSolverR0230.adaptive_checked_input)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ) (A : ArithmeticThetaAdaptiveSolverR0230.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → 0 < h → ∀ cs : List (ArithmeticThetaAdaptiveSolverR0230.Change n h), ∃ o : ArithmeticThetaAdaptiveSolverR0230.Result h, ArithmeticThetaAdaptiveSolverR0230.solveChanges A cs = some o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_checked_input
