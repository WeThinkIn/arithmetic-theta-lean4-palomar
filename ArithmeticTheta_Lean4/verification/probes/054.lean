import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `ArithmeticThetaFourTorsion
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaSchemeFourCharacterR0215
run_cmd Lean.activateScoped `ArithmeticThetaSchemeHodgeR0205
run_cmd Lean.activateScoped `ArithmeticThetaSchemeLevelR0204
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `S.presheaf
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_character)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → ∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A ∧ ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z ∧ (∀ a' : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M' a' → a' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val • a)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_character
