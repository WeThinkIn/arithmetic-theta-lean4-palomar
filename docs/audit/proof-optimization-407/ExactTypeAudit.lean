module
import all Definitions.Def_WeierstrassCurve_ProjModel_ThirdAddFormulas
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
run_cmd liftTermElabM do
  for (mod, n) in [(`Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas, ``WeierstrassProjModel.kw_lrSym_minor_YZ), (`Definitions.Def_WeierstrassCurve_ProjModel_ThirdAddFormulas, ``WeierstrassProjModel.kw_lrThird_minor_YZ)] do
    let current ← getConstInfo n
    let rel := mod.toString.replace "." "/"
    let expected : System.FilePath := "/home/Palomar/workspace/arithmetic-theta/project/.lake/build/lib/lean/" ++ rel ++ ".olean"
    let resolved ← findOLean mod
    unless resolved == expected do throwError "Wrong project import path {resolved}"
    let original : System.FilePath := "/home/Palomar/workspace/arithmetic-theta/evidence/proof-optimization-integration-407/baseline-objects/" ++ rel ++ ".olean"
    let (data, _) ← readModuleData original
    let mut matched := false
    for name in data.constNames, ci in data.constants do
      if name == n then
        unless ci.type == current.type do throwError "Original exact proposition AST differs {n}"
        unless ci.levelParams == current.levelParams do throwError "Universe parameters differ {n}"
        matched := true
    unless matched do throwError "Original declaration not found {n}"
    logInfo m!"PROJECT_IMPORT {resolved}; EXACT_ORIGINAL_TYPE_AST_MATCH {n} true; UNIVERSES_MATCH true"
#print axioms WeierstrassProjModel.kw_lrSym_minor_YZ
#print axioms WeierstrassProjModel.kw_lrThird_minor_YZ
