import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaElementary.rank_zero_image)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ, (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔ ∃ z : ℂ, f = PowerSeries.C z))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaElementary.rank_zero_image
