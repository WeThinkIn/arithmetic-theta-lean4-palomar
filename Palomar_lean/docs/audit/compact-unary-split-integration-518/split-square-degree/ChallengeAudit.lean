module
import all Challenge
import Lean
open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Challenge | throwError "Module not imported"
  let targets : List Name := [``WeierstrassProjModel.span_polynomial_isHomogeneousCR, ``HomogeneousIdealQuotientGrading.preDecompose_of_mem, ``WeierstrassProjModel.kwYEvalRingHom_comp_algebraMap, ``HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff, ``HomogeneousIdealQuotientGrading.quotDecompose_mk, ``WeierstrassProjModel.kwYEvalRingHom_mk_X1, ``ProjWeierstrassCubicPrime.isHomogeneous_polynomial, ``HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose, ``HomogeneousIdealQuotientGrading.gradedMonoidOfImages, ``HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem, ``HomogeneousIdealQuotientGrading.pieceHom_coe, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom, ``WeierstrassProjModel.kwYChartEval_section, ``ArithmeticThetaPalomarComponent485.componentIsOpen, ``ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_isIso, ``ArithmeticThetaComponentDegreeR0184.componentIntegral, ``ArithmeticThetaComponentDegreeR0184.componentLocallyNoetherian, ``ArithmeticThetaPalomarSplit516.splitSquareCoverDegree]
  let mut checked : Nat := 0
  let mut propagatedHoles : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axs ← collectAxioms name
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound || (true && a == `sorryAx)) do
      throwError "Unapproved axioms {name}: {axs}"
    if axs.contains `sorryAx then propagatedHoles := propagatedHoles + 1
    checked := checked + 1
    logInfo m!"DECL {name} AXIOMS {axs}"
  unless checked > 0 do throwError "No declarations inspected"
  for name in targets do
    let axs ← collectAxioms name
    if true then
      unless axs.contains `sorryAx do throwError "Expected target hole {name}"
    else
      unless !axs.contains `sorryAx do throwError "Unproved target {name}"
  let projectText ← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/scheme-four-character-frontier-425/project-modules.txt"
  let projectImports := env.header.modules.toList.filter (fun m => (projectText.splitOn "\n").contains m.module.toString)
  if true then
    unless projectImports.isEmpty do throwError "Challenge imports project modules"
  logInfo m!"AUDIT checked={checked} propagated_holes={propagatedHoles} project_imports={projectImports.length}"
