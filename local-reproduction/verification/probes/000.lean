import Lean
import BinaryOrthogonalExampleR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaFullSourceR0268
run_cmd Lean.activateScoped `ArithmeticThetaFullSourceR0268.binaryBasis
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalConsumerR0127
run_cmd Lean.activateScoped `Function
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaFullSourceR0268.binary_orthogonal_example)
  let expected ← Lean.Elab.Term.elabType (← `(term| ArithmeticThetaComputed.validGram ArithmeticThetaFullSourceR0268.binaryGram ∧ ArithmeticThetaFullSourceR0268.binaryBasis.det = 2 ∧ ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData ArithmeticThetaFullSourceR0268.binaryGram ArithmeticThetaFullSourceR0268.binaryBasis ArithmeticThetaFullSourceR0268.binaryNorms ∧ ∃ t : Fin 2 → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice ArithmeticThetaFullSourceR0268.binaryBasis, (∀ i, (t i).val = ArithmeticThetaFullSourceR0268.binaryRepresentatives i) ∧ Function.Bijective (fun i => ArithmeticThetaOrthogonalConsumerR0127.cosetClass ArithmeticThetaFullSourceR0268.binaryBasis (t i)) ∧ (∀ i j, ((ArithmeticThetaFullSourceR0268.binaryResidues i j : ℤ) : ℚ) = (ArithmeticThetaFullSourceR0268.binaryNorms j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram = ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 0) + ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 1) ∧ (∀ (D : ℕ) (hD : D ≠ 0), 92 ∣ D → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram) = ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 0 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 0 + ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 1 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 23)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaFullSourceR0268.binary_orthogonal_example
