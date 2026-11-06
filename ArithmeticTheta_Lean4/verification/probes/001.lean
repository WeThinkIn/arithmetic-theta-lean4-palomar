import Lean
import ConservativeImageConsumerR0268
run_cmd Lean.activateScoped `ArithmeticThetaArithmeticFieldR0231
run_cmd Lean.activateScoped `ArithmeticThetaCompactModularityR0209
run_cmd Lean.activateScoped `ArithmeticThetaCompactUnaryR0183
run_cmd Lean.activateScoped `ArithmeticThetaComputed
run_cmd Lean.activateScoped `ArithmeticThetaConservativeKernelR0189
run_cmd Lean.activateScoped `ArithmeticThetaElimination
run_cmd Lean.activateScoped `ArithmeticThetaFieldImageR0233
run_cmd Lean.activateScoped `ArithmeticThetaLatticeSectionsR0188
run_cmd Lean.activateScoped `ArithmeticThetaLevelCount
run_cmd Lean.activateScoped `G
run_cmd Lean.activateScoped `LinearMap
run_cmd Lean.activateScoped `PowerSeries
run_cmd Lean.activateScoped `Set
run_cmd Lean.activateScoped `Submodule
run_cmd Lean.activateScoped `U

set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``ArithmeticThetaFullSourceR0268.conservative_image_consumer)
  let expected ← Lean.Elab.Term.elabType (← `(term| ∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ B : ℕ, (if n = 0 then B = 0 else ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ B = ArithmeticThetaConservativeKernelR0189.cutoff A U ∧ (B : ℚ) = (n : ℚ) * ((ArithmeticThetaCompactUnaryR0183.exponent (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℕ) : ℚ)^U.count * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / 48) ∧ (∀ B' : ℕ, B ≤ B' → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) ∧ (∀ B' : ℕ, B ≤ B' → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B'))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B') t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B')).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B' t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B') j) ∧ (0 < n → FiniteDimensional ℚ (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) ∧ ∃ G : ArithmeticThetaArithmeticFieldR0231.MatrixData (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A, ArithmeticThetaCompactModularityR0209.ActualLevel G.root ∧ ∀ B' : ℕ, B ≤ B' → ArithmeticThetaFieldImageR0233.SectionImage (CyclotomicField (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) ℚ) A B' (ArithmeticThetaArithmeticFieldR0231.structureMap G) G.sections)))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms ArithmeticThetaFullSourceR0268.conservative_image_consumer
