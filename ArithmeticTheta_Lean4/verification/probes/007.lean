import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `Matrix
run_cmd Lean.activateScoped `Nat

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaDet80.actual_minor_determinant)
  let expected ← Lean.Elab.Term.elabType (← `(term| Matrix.det ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 4))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaDet80.actual_minor_determinant
