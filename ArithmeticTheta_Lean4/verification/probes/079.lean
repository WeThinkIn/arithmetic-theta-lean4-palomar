import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaGeneralDPlusR0242
run_cmd Lean.activateScoped `ArithmeticThetaRank16
run_cmd Lean.activateScoped `Module

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ n : ℕ, 8 ∣ n → ArithmeticThetaComputed.validGram (ArithmeticThetaRank16.latticeGram n) ∧ (ArithmeticThetaRank16.latticeGram n).det = 1 ∧ (∀ v : Fin n → ℚ, v ∈ ArithmeticThetaGeneralDPlusR0242.lattice n ↔ ArithmeticThetaRank16.originalDPlus n v) ∧ (∃ b : Module.Basis (Fin n) ℤ (ArithmeticThetaGeneralDPlusR0242.lattice n), ∀ (j i : Fin n), (b j).val i = ArithmeticThetaRank16.latticeBasis n i j) ∧ (∀ v : Fin n → ℚ, ArithmeticThetaRank16.originalDPlus n v → ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular
