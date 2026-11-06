import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `Finset
run_cmd Lean.activateScoped `LaurentPolynomial
run_cmd Lean.activateScoped `PowerSeries

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaDurfee.formal_jacobi_triple_product)
  let expected ← Lean.Elab.Term.elabType (← `(term| (PowerSeries.mk (fun e => PowerSeries.coeff e ((1 + PowerSeries.C (LaurentPolynomial.T 1)) * ∏ j ∈ Finset.range e, (1 - PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j + 1)) : PowerSeries (LaurentPolynomial ℤ)))) = PowerSeries.mk (fun d => ∑ k ∈ Finset.Icc (-(d : ℤ)) ((d : ℤ) + 1), if k * (k - 1) = 2 * (d : ℤ) then (LaurentPolynomial.T k : LaurentPolynomial ℤ) else 0)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaDurfee.formal_jacobi_triple_product
