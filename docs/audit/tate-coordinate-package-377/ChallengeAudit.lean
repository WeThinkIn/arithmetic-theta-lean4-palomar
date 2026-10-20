module
public import Challenge
public meta import Lean
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let projectText ← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/tate-coordinate-frontier-376/project-modules.txt"
  let projectModules := projectText.splitOn "\n"
  let imported := env.header.modules.toList.map (fun m => m.module.toString)
  let projectImports := imported.filter projectModules.contains
  unless projectImports.isEmpty do throwError "Project imports in Challenge: {projectImports}"
  let targets := [``ArithmeticThetaPalomarCoordinates377.algebraic_tate_coordinates,
    ``ArithmeticThetaPalomarCoordinates377.coordinate_exact_poles,
    ``ArithmeticThetaPalomarCoordinates377.algebraic_model_cubic,
    ``ArithmeticThetaPalomarCoordinates377.global_normalized_differential]
  let mut checked := #[]
  let mut holes := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if env.header.modules[idx]!.module != `Challenge then continue
    let axioms ← Lean.collectAxioms n
    let allowed := if targets.contains n then
      [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
      else [``propext, ``Classical.choice, ``Quot.sound]
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} for {n}"
    if axioms.contains ``sorryAx then holes := holes.push n.toString
    checked := checked.push (Json.mkObj [("name",toJson n.toString),("axioms",toJson (axioms.map Name.toString))])
  unless holes.size == 4 do throwError "Unexpected target-hole count {holes.size}"
  logInfo (Json.compress (Json.mkObj [("project_imports",toJson projectImports),
    ("checked_count",toJson checked.size),("target_holes",toJson holes),("checked",toJson checked)]))
