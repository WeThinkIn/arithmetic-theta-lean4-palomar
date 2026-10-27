import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaGlobalFourTorsionR0190
run_cmd Lean.activateScoped `ArithmeticThetaOpenHodgeR0180
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaTateCuspsR0181
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 0 < L → 4 ∣ L → ∀ (E : ArithmeticThetaTateCuspsR0181.TateLevel k L) (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L), ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ → ∀ a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L) E.law L E.marking a → (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧ a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ)) ∧ (∀ ζ : k, IsPrimitiveRoot ζ L → ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ E → a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k L ^ 2)) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior
