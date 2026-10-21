module
import all Solution
import Lean
open Lean Elab Command Meta
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
  let base := "/home/Palomar/workspace/arithmetic-theta/evidence/component-discriminant-package-509/Challenge"
  let parts ← readModuleDataParts #[⟨base ++ ".olean"⟩, ⟨base ++ ".olean.server"⟩, ⟨base ++ ".olean.private"⟩]
  let env ← getEnv
  let targets : List Name := [``WeierstrassProjModel.span_polynomial_isHomogeneousCR, ``HomogeneousIdealQuotientGrading.preDecompose_of_mem, ``WeierstrassProjModel.kwYEvalRingHom_comp_algebraMap, ``HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff, ``HomogeneousIdealQuotientGrading.quotDecompose_mk, ``WeierstrassProjModel.kwYEvalRingHom_mk_X1, ``ProjWeierstrassCubicPrime.isHomogeneous_polynomial, ``HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose, ``HomogeneousIdealQuotientGrading.gradedMonoidOfImages, ``HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem, ``HomogeneousIdealQuotientGrading.pieceHom_coe, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom, ``WeierstrassProjModel.kwYChartEval_section, ``ArithmeticThetaPalomarComponent485.componentIsOpen, ``ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_isIso, ``ArithmeticThetaComponentDegreeR0184.componentIntegral, ``ArithmeticThetaComponentDegreeR0184.componentLocallyNoetherian, ``ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor, ``ArithmeticThetaPalomarD2_509.componentDiscriminantDivisor]
  let mut source : NameMap ConstantInfo := {}
  for (data, _) in parts do
    for ci in data.constants do source := source.insert ci.name ci
  for name in targets do
    let some ci := source.find? name | throwError "Target missing in Challenge: {name}"
    let some si := env.find? name | throwError "Target missing in Solution: {name}"
    unless ci.levelParams == si.levelParams do throwError "Universe mismatch: {name}"
    unless (← isProp ci.type) do throwError "Non-proposition target: {name}"
    unless (← withTransparency .all <| isDefEq ci.type si.type) do
      throwError "Target type mismatch: {name}"
    let axs ← collectAxioms name
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unapproved target axioms {name}: {axs}"
    logInfo m!"TARGET_TYPE_UNIVERSES_AND_STANDARD_AXIOMS {name}"
  logInfo m!"ALL_EXPLICIT_TARGETS_CHECKED {targets.length}"
