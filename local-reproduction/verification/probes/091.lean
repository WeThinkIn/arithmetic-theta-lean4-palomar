import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaTateIdentities
run_cmd Lean.activateScoped `ArithmeticThetaTateSeries
run_cmd Lean.activateScoped `ArithmeticThetaUnaryProduct
run_cmd Lean.activateScoped `HahnSeries
run_cmd Lean.activateScoped `Int
run_cmd Lean.activateScoped `PowerSeries
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaTateIdentities.general_annular_addition)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ {k : Type u} [Field k] [CharZero k], ∀ (d i j : ℕ) (a b : k), ArithmeticThetaTateSeries.Admissible d i a → ArithmeticThetaTateSeries.Admissible d j b → (ArithmeticThetaTateSeries.toLaurent k (ArithmeticThetaTateSeries.tateX d i (a : k)) - ArithmeticThetaTateSeries.toLaurent k (ArithmeticThetaTateSeries.tateX d j (b : k))) * (ArithmeticThetaTateIdentities.gammaLaurent d (i:ℤ) a)^2 * (ArithmeticThetaTateIdentities.gammaLaurent d (j:ℤ) b)^2 = -HahnSeries.single (j:ℤ) b * (ArithmeticThetaTateSeries.toLaurent k (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d)))^4 * ArithmeticThetaTateIdentities.gammaLaurent d ((i:ℤ)-(j:ℤ)) (a/b) * ArithmeticThetaTateIdentities.gammaLaurent d ((i:ℤ)+(j:ℤ)) (a*b)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaTateIdentities.general_annular_addition
