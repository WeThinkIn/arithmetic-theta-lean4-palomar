import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaCompactUnaryR0183
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaLatticeSectionsR0188
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaSectionOrder
run_cmd Lean.activateScoped `ArithmeticThetaSharpKernelR0195

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSharpKernelR0195.sharp_geometric_cutoff)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaSharpKernelR0195.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaSharpKernelR0195.cutoff A) → ArithmeticThetaComputed.thetaMap A c = 0))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSharpKernelR0195.sharp_geometric_cutoff
