import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComponentDegreeR0184
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaLevelCount
run_cmd Lean.activateScoped `Matrix
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound
