import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaIsogenyHalfLinesR0193
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaIsogenyHalfLinesR0193.isogeny_alpha_all_cusp_orders)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D, ArithmeticThetaIsogenyHalfLinesR0193.AllCuspOrders k L m D A))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.isogeny_alpha_all_cusp_orders
