import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaComponentDegreeR0184
run_cmd Lean.activateScoped `ArithmeticThetaCurveDegree
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaLineRoot
run_cmd Lean.activateScoped `ArithmeticThetaSectionOrder
run_cmd Lean.activateScoped `Matrix
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaComponentDegreeR0184.component_hodge_power_degree)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) ι) (t : (ArithmeticThetaComponentDegreeR0184.power k L D X x H n).presheaf.obj (Opposite.op ⊤)) (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ), t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) C t E → 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) = (n : ℤ) * (2*L : ℕ) * (Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) : ℤ) ∧ 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) ≤ (n : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaComponentDegreeR0184.component_hodge_power_degree
