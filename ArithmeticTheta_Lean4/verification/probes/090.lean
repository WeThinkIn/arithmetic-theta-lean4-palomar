import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaElimination
run_cmd Lean.activateScoped `LinearMap
run_cmd Lean.activateScoped `Module
run_cmd Lean.activateScoped `Set
run_cmd Lean.activateScoped `Submodule

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaDegreeAssembly.certified_theta_image_data)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ W : Submodule ℂ (Fin h → ℂ), W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaDegreeAssembly.certified_theta_image_data
