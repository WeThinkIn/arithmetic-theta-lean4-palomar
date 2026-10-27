import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAdaptiveSolverR0230
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `o

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAdaptiveSolverR0230.adaptive_universal_solver)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h d : ℕ) (A : ArithmeticThetaAdaptiveSolverR0230.Matrices n h) (R : Matrix (Fin h) (Fin d) ℚ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ArithmeticThetaAdaptiveSolverR0230.Relations A R → 0 < h → ∃ o : ArithmeticThetaAdaptiveSolverR0230.Result h, ArithmeticThetaAdaptiveSolverR0230.solve A R = some o ∧ o.cutoff ≤ ArithmeticThetaAdaptiveSolverR0230.bound A ∧ ArithmeticThetaAdaptiveSolverR0230.Correct A o ∧ o.cutoff ∈ ArithmeticThetaAdaptiveSolverR0230.schedule (ArithmeticThetaAdaptiveSolverR0230.bound A) ∧ (o.cutoff = ArithmeticThetaAdaptiveSolverR0230.bound A ∨ ArithmeticThetaAdaptiveSolverR0230.early A R o.cutoff = true) ∧ ∀ b ∈ ArithmeticThetaAdaptiveSolverR0230.schedule (ArithmeticThetaAdaptiveSolverR0230.bound A), b < o.cutoff → ArithmeticThetaAdaptiveSolverR0230.early A R b = false))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAdaptiveSolverR0230.adaptive_universal_solver
