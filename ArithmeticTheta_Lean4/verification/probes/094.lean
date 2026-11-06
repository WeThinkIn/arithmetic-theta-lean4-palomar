import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaLaurentNormR0064
run_cmd Lean.activateScoped `ArithmeticThetaNormFiniteR0063
run_cmd Lean.activateScoped `Nat
run_cmd Lean.activateScoped `i
run_cmd Lean.activateScoped `j

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaLaurentNormR0064.powered_gamma_norm)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (K : Type) [Field K] [CharZero K] (c d : ℕ) (ζ : K), 1 < c → 0 < d → Nat.Coprime c d → IsPrimitiveRoot ζ d → ∀ (H : Fin d → Fin d → ArithmeticThetaLaurentNormR0064.Series K) (b : ArithmeticThetaLaurentNormR0064.Series K), (∀ i j : Fin d, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff K) d (c * i.val) (ArithmeticThetaLaurentNormR0064.a K ζ j.val c) (H i j)) → ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff K) d 0 (ArithmeticThetaLaurentNormR0064.w K ^ (c * d)) b → (∏ i : Fin d, ∏ j : Fin d, H i j) = (-1 : ArithmeticThetaLaurentNormR0064.Series K) ^ (-ArithmeticThetaNormFiniteR0063.S c d) * ArithmeticThetaLaurentNormR0064.z K d ^ (-(c : ℤ) * ArithmeticThetaNormFiniteR0063.S c d) * ArithmeticThetaLaurentNormR0064.Q K d ^ (-ArithmeticThetaNormFiniteR0063.E c d) * b))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaLaurentNormR0064.powered_gamma_norm
