import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaGlobalProjectiveRatiosR0266
run_cmd Lean.activateScoped `ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaTateCuspsR0181
run_cmd Lean.activateScoped `Vd

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGlobalProjectiveRatiosR0266.global_arithmetic_projective_ratios)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGlobalProjectiveRatiosR0266.global_arithmetic_projective_ratios
