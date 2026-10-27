import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `A
run_cmd Lean.activateScoped `AlgebraicGeometry
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme
run_cmd Lean.activateScoped `AlgebraicGeometry.Scheme.Modules
run_cmd Lean.activateScoped `ArithmeticThetaBoundaryHodgeR0182
run_cmd Lean.activateScoped `ArithmeticThetaEvenMarkingTorsorR0216
run_cmd Lean.activateScoped `ArithmeticThetaKeyTateR0220
run_cmd Lean.activateScoped `ArithmeticThetaLocalWeierstrassR0203
run_cmd Lean.activateScoped `ArithmeticThetaMultiplierKeyR0217
run_cmd Lean.activateScoped `ArithmeticThetaPhaseFreeKeyR0219
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaSchemeHodgeR0205
run_cmd Lean.activateScoped `ArithmeticThetaTateCuspsR0181
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `E
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `S
run_cmd Lean.activateScoped `SheafOfModules

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaKeyTateR0220.phase_free_key_tate_normalization)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (k : Type) [Field k] [CharZero k] (N : ℕ), 0 < N → 4 ∣ N → ∀ (T : ArithmeticThetaTateCuspsR0181.TateLevel k N), ∀ (S : AlgebraicGeometry.Scheme) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E) (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ → ∀ (A : ArithmeticThetaPhaseFreeKeyR0219.MarkedTest E P) (B : ArithmeticThetaKeyTateR0220.TateTest k N T A.family A.marking) (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback A.map).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent A.family)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c → ∀ (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k N), ArithmeticThetaBoundaryHodgeR0182.Normalized k N δ → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaKeyTateR0220.tateProduct k N T E P L A B) ⊤ (ArithmeticThetaKeyTateR0220.productFrame k N T E P L m A B δ) ∧ ArithmeticThetaKeyTateR0220.Expansion k N T E P L m A B δ (ArithmeticThetaKeyTateR0220.productAt k N T E P L A B c (κ.hom.app ⊤ (ArithmeticThetaMultiplierKeyR0217.evaluationSquare E P e)))))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaKeyTateR0220.phase_free_key_tate_normalization
