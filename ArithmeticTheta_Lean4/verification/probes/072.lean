import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `A'
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaArithmeticSectionsR0236
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryConstantsR0235
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaCompactUnaryR0183
run_cmd Lean.activateScoped `ArithmeticThetaLevelCompactificationR0179
run_cmd Lean.activateScoped `ArithmeticThetaTensorPower
run_cmd Lean.activateScoped `C
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `H
run_cmd Lean.activateScoped `J
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `X
run_cmd Lean.activateScoped `Y
run_cmd Lean.activateScoped `a
run_cmd Lean.activateScoped `b

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaArithmeticSectionsR0236.field_unary_compact_naturality)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l (ArithmeticThetaCompactUnaryR0183.level N) E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k (ArithmeticThetaCompactUnaryR0183.level N) ι D E X Y) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l (ArithmeticThetaCompactUnaryR0183.level N) E Y), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ArithmeticThetaBoundaryHodgeR0182.Canonical l (ArithmeticThetaCompactUnaryR0183.level N) J → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical J → ∀ (a b : Fin N), (a.val ≠ 0 ∨ b.val ≠ 0) → ∀ (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (A' : ArithmeticThetaCompactUnaryR0183.OpenPower l m N E a b) (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤)) (t : (ArithmeticThetaTensorPower.tensorPower Y.space J.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaBoundaryHodgeR0182.restrictPower k (ArithmeticThetaCompactUnaryR0183.level N) H (ArithmeticThetaCompactUnaryR0183.weight N) s = ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ → ArithmeticThetaBoundaryHodgeR0182.restrictPower l (ArithmeticThetaCompactUnaryR0183.level N) J (ArithmeticThetaCompactUnaryR0183.weight N) t = ArithmeticThetaBoundaryHodgeR0182.pullToOpen l (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A'.section_ → ∃ eH : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback C.compactMap).obj H.line) (J.line), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J eH ∧ ArithmeticThetaArithmeticSectionsR0236.powerTransport C.compactMap H.line J.line eH (ArithmeticThetaCompactUnaryR0183.weight N) (s) = t))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaArithmeticSectionsR0236.field_unary_compact_naturality
