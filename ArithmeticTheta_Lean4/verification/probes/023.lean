import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaAlgebraicCoordinatesR0143
run_cmd Lean.activateScoped `ArithmeticThetaAlgebraizedMarkedLineR0136
run_cmd Lean.activateScoped `ArithmeticThetaCubicModelR0144
run_cmd Lean.activateScoped `ArithmeticThetaIdentitySectionsR0138
run_cmd Lean.activateScoped `ArithmeticThetaInfinitesimalPolygonR0129
run_cmd Lean.activateScoped `ArithmeticThetaProjectiveEffectivityR0135
run_cmd Lean.activateScoped `M
run_cmd Lean.activateScoped `Quiver
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaCubicModelR0144.algebraic_model_cubic)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ArithmeticThetaCubicModelR0144.ModelCubic k M s X Y))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaCubicModelR0144.algebraic_model_cubic
