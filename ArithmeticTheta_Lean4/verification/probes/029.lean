import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalAlgorithm
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalConsumerR0127
run_cmd Lean.activateScoped `ArithmeticThetaSchrodingerR0119
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaOrthogonalConsumerR0127.computed_family_formal_unary_consumer)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (D : ℕ) (hD : D ≠ 0), (∀ (i : Fin h) (j : Fin n), 2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) ∣ D) → ∃ (t : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i))) (ν : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → (j : Fin n) → Fin (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) (hw : ∀ (i : Fin h) (j : Fin n), D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) ≠ 0), (∀ i, ArithmeticThetaOrthogonalConsumerR0127.Representatives (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)) (t i)) ∧ (∀ (i : Fin h) (a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs) (j : Fin n), ∃ z : ℤ, ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (t i a).val j = ((ν i a j).val : ℚ) + ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (z : ℚ)) ∧ (∀ c : Fin h → ℂ, PowerSeries.expand D hD (ArithmeticThetaComputed.thetaMap A c) = ∑ i : Fin h, c i • (∑ a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs, ∏ j : Fin n, PowerSeries.expand (D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j))) (hw i j) (ArithmeticThetaSchrodingerR0119.unary ℂ (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) (ν i a j))))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaOrthogonalConsumerR0127.computed_family_formal_unary_consumer
