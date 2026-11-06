import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaLatticeSectionsR0188
run_cmd Lean.activateScoped `ArithmeticThetaSharpKernelR0195
run_cmd Lean.activateScoped `LinearMap
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → (∀ B : ℕ, ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ArithmeticThetaSharpKernelR0195.cutoff A = 0 ∧ ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel
