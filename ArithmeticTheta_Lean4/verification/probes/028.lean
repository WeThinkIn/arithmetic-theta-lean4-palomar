import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalConsumerR0127
run_cmd Lean.activateScoped `B
run_cmd Lean.activateScoped `B.det
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaOrthogonalConsumerR0127.source_orthogonal_factorization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ t : Fin B.det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B, ArithmeticThetaOrthogonalConsumerR0127.Representatives B t → ∃ ν : Fin B.det.natAbs → Fin n → ℤ, (∀ i j, (ν i j : ℚ) = (m j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ A = ∑ i : Fin B.det.natAbs, ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m (t i).val ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ A) = ∑ i : Fin B.det.natAbs, ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν i j))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaOrthogonalConsumerR0127.source_orthogonal_factorization
