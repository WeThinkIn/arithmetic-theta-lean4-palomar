module
import all Solution
import Lean
open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Solution | throwError "Module not imported"
  let targets := [``ArithmeticThetaPalomarSchemePhase433.localDataExists, ``ArithmeticThetaPalomarSchemePhase433.arbitrarySplitFiberBasis, ``ArithmeticThetaPalomarSchemePhase433.schemeMillerPhase]
  let mut checked : Nat := 0
  let mut propagatedHoles : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axs ← collectAxioms name
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound || (false && a == `sorryAx)) do
      throwError "Unapproved axioms {name}: {axs}"
    if axs.contains `sorryAx then propagatedHoles := propagatedHoles + 1
    checked := checked + 1
    logInfo m!"DECL {name} AXIOMS {axs}"
  unless checked > 0 do throwError "No declarations inspected"
  for name in targets do
    let axs ← collectAxioms name
    if false then
      unless axs.contains `sorryAx do throwError "Expected target hole {name}"
    else
      unless !axs.contains `sorryAx do throwError "Unproved target {name}"
  let projectText ← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/scheme-four-character-frontier-425/project-modules.txt"
  let projectImports := env.header.modules.toList.filter (fun m => (projectText.splitOn "\n").contains m.module.toString)
  if false then
    unless projectImports.isEmpty do throwError "Challenge imports project modules"
  logInfo m!"AUDIT checked={checked} propagated_holes={propagatedHoles} project_imports={projectImports.length}"
