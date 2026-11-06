module
import all Solution
import Lean
open Lean Elab Command Meta
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
  let base := "/home/Palomar/workspace/arithmetic-theta/evidence/compact-key-surface-469/Challenge"
  let parts ← readModuleDataParts #[⟨base ++ ".olean"⟩, ⟨base ++ ".olean.server"⟩, ⟨base ++ ".olean.private"⟩]
  let env ← getEnv
  let targets : List Name := [``ArithmeticThetaPalomarGlobalFrame401.canonicalDifferentialMap, ``ArithmeticThetaPalomarGlobalFrame401.normalizedFrameExists, ``ArithmeticThetaPalomarGlobalFrame401.hodgeGeneratorFrame, ``ArithmeticThetaPalomarGlobalFrame401.normalizedFrameExistsUnique, ``ArithmeticThetaPalomarConormal436.canonicalConormalMap, ``ArithmeticThetaPalomarSchemeAlpha437.alphaExists, ``ArithmeticThetaPalomarSchemeAlpha437.schemeAlphaCharacter, ``ArithmeticThetaPalomarMultiplier450.phaseFreeMultiplier, ``ArithmeticThetaPalomarMultiplier450.phaseFreeMultiplierBaseChange, ``ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor, ``ArithmeticThetaPalomarAlphaDescent459.phaseFreeAlphaDescent, ``SheafOfModules.presheafW_isMonoidal, ``ArithmeticThetaPalomarDual465.canonicalGlobalSectionsEquiv, ``ArithmeticThetaPalomarKey466.phaseFreeKey, ``ArithmeticThetaPalomarKey466.phaseFreeKeyNaturality, ``PresheafOfModules.uncurry'_curry', ``WeierstrassProjModel.span_polynomial_isHomogeneousCR, ``HomogeneousIdealQuotientGrading.preDecompose_of_mem, ``WeierstrassProjModel.kwYEvalRingHom_comp_algebraMap, ``HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff, ``HomogeneousIdealQuotientGrading.quotDecompose_mk, ``WeierstrassProjModel.kwYEvalRingHom_mk_X1, ``PresheafOfModules.InternalHom.map_id_apply, ``ProjWeierstrassCubicPrime.isHomogeneous_polynomial, ``HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid, ``PresheafOfModules.curry'_uncurry', ``PresheafOfModules.uncurryApp_tmul, ``PresheafOfModules.ihomObj_map_val, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose, ``PresheafOfModules.uncurry'_app_tmul, ``HomogeneousIdealQuotientGrading.gradedMonoidOfImages, ``PresheafOfModules.InternalHom.naturalFamilies_ext, ``PresheafOfModules.tensorObj_map_tmul', ``HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem, ``HomogeneousIdealQuotientGrading.pieceHom_coe, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom, ``WeierstrassProjModel.kwYChartEval_section]
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
