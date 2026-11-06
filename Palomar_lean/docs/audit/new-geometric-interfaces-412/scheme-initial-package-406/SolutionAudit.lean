module
public import Solution
public meta import Lean
set_option maxRecDepth 8192
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets := [``ArithmeticThetaPalomarNormalInitial381.initialTensorExistsUnique,
    ``ArithmeticThetaPalomarDifferential365.normalizedConormalHodge,
    ``ArithmeticThetaPalomarWeierstrass373.projectiveGeometry,
    ``ArithmeticThetaPalomarWeierstrass373.canonicalWeierstrassHodge,
    ``ArithmeticThetaPalomarSchemePower383.canonicalSchemePower,
    ``ArithmeticThetaPalomarFullScheme385.canonicalWPower,
    ``ArithmeticThetaPalomarFullScheme385.canonicalAffinePower,
    ``ArithmeticThetaPalomarFullScheme385.normal_test_exists,
    ``ArithmeticThetaPalomarFullScheme385.scheme_exists,
    ``ArithmeticThetaPalomarFullScheme385.scheme_naturality,
    ``ArithmeticThetaPalomarKatoSupport394.normalModelExists,
    ``ArithmeticThetaPalomarKatoSupport394.schemeUnitExists,
    ``ArithmeticThetaPalomarSchemeInitial406.identityChartCoverExists,
    ``ArithmeticThetaPalomarSchemeInitial406.schemeFiveInitialCharacterization]
  let mut checked := #[]
  let mut directHoles := #[]
  for (n,ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless env.header.modules[idx]!.module == `Solution do continue
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] ||
        (false && ax == ``sorryAx) do throwError "unexpected axiom {ax} for {n}"

    let directSorry := targets.contains n && axs.contains ``sorryAx
    if directSorry then
      unless false && targets.contains n do throwError "extra direct sorry at {n}"
      directHoles := directHoles.push n.toString
    checked := checked.push (Json.mkObj [("name",toJson n.toString),("axioms",toJson (axs.map Name.toString))])
  if false then
    unless directHoles.size == 14 do throwError "expected14 direct target holes, got {directHoles.size}"
  let projectText ← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/period-one-frontier-395/project-modules.txt"
  let imports := env.header.modules.toList.map (fun m => m.module.toString)
  let projectImports := imports.filter (projectText.splitOn "\n").contains
  if false then
    unless projectImports.isEmpty do throwError "project imports found"
  logInfo (Json.compress (Json.mkObj [("checked_count",toJson checked.size),
    ("checked",toJson checked),("target_holes",toJson directHoles),
    ("project_import_count",toJson projectImports.length)]))
