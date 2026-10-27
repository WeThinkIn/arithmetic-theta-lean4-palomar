import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaOrthogonalConsumerR0127
run_cmd Lean.activateScoped `B
run_cmd Lean.activateScoped `B.det
run_cmd Lean.activateScoped `Int
run_cmd Lean.activateScoped `LinearMap
run_cmd Lean.activateScoped `Matrix
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `t

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaOrthogonalConsumerR0127.rational_preimage_cosets)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 → ∃ E : ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B ≃+ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)), (∀ (t : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B) (x : Fin n → ℤ), (B.map (Int.castRingHom ℚ)).mulVec t.val = ArithmeticThetaOrthogonalConsumerR0127.castVec n x → E (ArithmeticThetaOrthogonalConsumerR0127.cosetClass B t) = (LinearMap.range (Matrix.mulVecLin B)).mkQ x) ∧ Finite (ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B) ∧ Nat.card (ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B) = B.det.natAbs ∧ ∃ t : Fin B.det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B, ArithmeticThetaOrthogonalConsumerR0127.Representatives B t))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaOrthogonalConsumerR0127.rational_preimage_cosets
