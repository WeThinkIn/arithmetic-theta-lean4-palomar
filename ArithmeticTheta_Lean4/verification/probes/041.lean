import Lean
import FullSourceIntegrationR0268
run_cmd Lean.activateScoped `ArithmeticThetaFullLevelCoverR0175
run_cmd Lean.activateScoped `ArithmeticThetaGlobalFourTorsionR0190
run_cmd Lean.activateScoped `ArithmeticThetaRelativeDiscriminantR0171
run_cmd Lean.activateScoped `ArithmeticThetaRelativeKatoNaturalityR0170
run_cmd Lean.activateScoped `ArithmeticThetaRelativeKatoR0169
run_cmd Lean.activateScoped `CategoryTheory
run_cmd Lean.activateScoped `CategoryTheory.CategoryStruct
run_cmd Lean.activateScoped `M
run_cmd Lean.activateScoped `M.x
run_cmd Lean.activateScoped `M.y
run_cmd Lean.activateScoped `Ms
run_cmd Lean.activateScoped `Ms.x
run_cmd Lean.activateScoped `Ms.y
run_cmd Lean.activateScoped `Opposite
run_cmd Lean.activateScoped `Quiver
run_cmd Lean.activateScoped `W
run_cmd Lean.activateScoped `Ws
universe u
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaGlobalFourTorsionR0190.relative_alpha_naturality)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), (∃! a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W) ⊤ a) ∧ (∀ (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (Ms : ArithmeticThetaFullLevelCoverR0175.FullLevel S Ws Gs L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b), CategoryTheory.CategoryStruct.comp (Ms.x.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.x.val) → CategoryTheory.CategoryStruct.comp (Ms.y.val) (b) = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (M.y.val) → ∀ (a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤)) (as_ : (ArithmeticThetaRelativeDiscriminantR0171.Hodge S Ws).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L M a → ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha S Ws Gs L Ms as_ → ArithmeticThetaGlobalFourTorsionR0190.pullAlpha R W G S Ws Gs ι b hb a = as_)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaGlobalFourTorsionR0190.relative_alpha_naturality
