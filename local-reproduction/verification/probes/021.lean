import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAlgebraicCoordinatesR0143
run_cmd Lean.activateScoped `ArithmeticThetaAlgebraizedMarkedLineR0136
run_cmd Lean.activateScoped `ArithmeticThetaIdentitySectionsR0138
run_cmd Lean.activateScoped `ArithmeticThetaInfinitesimalPolygonR0129
run_cmd Lean.activateScoped `ArithmeticThetaProjectiveEffectivityR0135
run_cmd Lean.activateScoped `M
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ odd : Bool, ∃! φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates
