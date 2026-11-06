import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAdaptiveSolverR0230
run_cmd Lean.activateScoped `ArithmeticThetaComputed

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAdaptiveSolverR0230.checked_basis_change_relations)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ) (A : ArithmeticThetaAdaptiveSolverR0230.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ cs : List (ArithmeticThetaAdaptiveSolverR0230.Change n h), ArithmeticThetaAdaptiveSolverR0230.Relations A (ArithmeticThetaAdaptiveSolverR0230.changeRelations A cs)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAdaptiveSolverR0230.checked_basis_change_relations
