import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaCompactUnaryR0183
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaLatticeSectionsR0188
run_cmd Lean.activateScoped `ArithmeticThetaLevelCount
run_cmd Lean.activateScoped `ArithmeticThetaSharpKernelR0195
run_cmd Lean.activateScoped `I

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSharpKernelR0195.distinct_norm_sharp_arithmetic)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → 0 < ArithmeticThetaSharpKernelR0195.normCount A ∧ ∃ I : ArithmeticThetaSharpKernelR0195.NormIndex A, ArithmeticThetaSharpKernelR0195.IndexesNorms A I ∧ (∀ i, 0 < I.norm i ∧ Even (I.norm i) ∧ I.norm i ∣ ArithmeticThetaLatticeSectionsR0188.commonN A ∧ 8*I.norm i ∣ ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ∧ ((ArithmeticThetaSharpKernelR0195.cutoff A : ℕ) : ℚ) ≤ (n : ℚ) * 2^(ArithmeticThetaSharpKernelR0195.normCount A-1) * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / (48*(ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℚ)) ∧ (n : ℚ) * 2^(ArithmeticThetaSharpKernelR0195.normCount A-1) * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / (48*(ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℚ)) < (ArithmeticThetaSharpKernelR0195.cutoff A : ℚ)+1))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSharpKernelR0195.distinct_norm_sharp_arithmetic
