import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaComponentDegreeR0184
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaNormalizedSections
run_cmd Lean.activateScoped `ArithmeticThetaSquareLinesR0192
run_cmd Lean.activateScoped `ArithmeticThetaTensorPower
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSquareLinesR0192.compact_alpha_canonical_half_line)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (a : (H.line).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSquareLinesR0192.IsCompactAlpha k L D X H a → ∀ x : X.space, ∃ (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ) (hE : ∀ y, 0 ≤ E y) (hN : ArithmeticThetaNormalizedSections.NormalAffine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaSquareLinesR0192.HalfAlphaDivisor k L D X H x a E ∧ AlgebraicGeometry.Scheme.Modules.IsInvertible (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line ∧ ∃ β : CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H), β.hom.app ⊤ (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2 ⊤ (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).section_) = ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ∧ ArithmeticThetaSquareLinesR0192.AlphaHalfBranch k L D X H x (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN) β))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSquareLinesR0192.compact_alpha_canonical_half_line
