import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaComponentDegreeR0184
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaSharpCoverR0194
run_cmd Lean.activateScoped `ArithmeticThetaSimultaneousUnaryR0187
run_cmd Lean.activateScoped `ArithmeticThetaSquareLinesR0192
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaCyclotomicModularityR0239.split_square_cover_degree)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (x : X.space) (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H)) (b n : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.projection k L D X x) b), ArithmeticThetaSharpCoverR0194.SquareCoverDegree k L D X H x J b n C))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaCyclotomicModularityR0239.split_square_cover_degree
