import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaArithmeticSectionsR0236
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryConstantsR0235
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaOpenHodgeR0180
run_cmd Lean.activateScoped `ArithmeticThetaTensorPower
run_cmd Lean.activateScoped `D
run_cmd Lean.activateScoped `D.atlas
run_cmd Lean.activateScoped `D.atlas.descent
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `X

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaArithmeticSectionsR0236.field_compact_discriminant)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ d : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d → ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaArithmeticSectionsR0236.RealizesDiscriminant k L H d s))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaArithmeticSectionsR0236.field_compact_discriminant
