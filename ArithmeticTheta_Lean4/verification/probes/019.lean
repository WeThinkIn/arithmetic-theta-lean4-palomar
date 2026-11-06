import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `LinearMap
run_cmd Lean.activateScoped `Module

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaEarlyAssembly.actual_earlier_certificate)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ≤ LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin) ∧ ((ArithmeticThetaComputed.coefficientMatrix A B).rank = h → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = ⊥) ∧ (∀ W : Submodule ℂ (Fin h → ℂ), (∀ c ∈ W, ArithmeticThetaComputed.thetaMap A c = 0) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → W = LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ∧ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaEarlyAssembly.actual_earlier_certificate
