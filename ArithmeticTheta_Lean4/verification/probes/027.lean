import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalConsumerR0127
run_cmd Lean.activateScoped `Int
run_cmd Lean.activateScoped `PowerSeries
run_cmd Lean.activateScoped `t

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaOrthogonalConsumerR0127.individual_coset_integral_product)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ (t : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B) (ν : Fin n → ℤ), (∀ j, (ν j : ℚ) = (m j : ℚ) * t.val j) → (∀ r : Fin n → ℤ, (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) → ∃ a : ℕ, (∑ j : Fin n, (r j : ℚ)^2 / (2 * (m j : ℚ))) = (a : ℚ)) ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m t.val) = ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν j))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaOrthogonalConsumerR0127.individual_coset_integral_product
