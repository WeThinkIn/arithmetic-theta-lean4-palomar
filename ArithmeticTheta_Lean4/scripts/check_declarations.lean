import Lean

/-! Compare all original named declarations in two compiled proof environments.

Usage: lean --run scripts/check_declarations.lean BASELINE_OBJECTS CURRENT_OBJECTS
  PINNED_DEPENDENCIES metadata/dependencies.json OUTPUT_REPORT.json

Both object directories must contain all 1,199 proof modules. Each environment
loads its own GoalRoot with the same pinned dependencies and Lean standard
library. No candidate import falls back to the baseline build. Types and
original definition bodies must be definitionally equal; kinds and universe
parameters must be identical. Internal generated names are excluded.
-/

open Lean Meta

def kind : ConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo _ => 1 | .thmInfo _ => 2
  | .opaqueInfo _ => 3 | .quotInfo _ => 4 | .inductInfo _ => 5
  | .ctorInfo _ => 6 | .recInfo _ => 7

def main (args : List String) : IO UInt32 := do
  let [oldPath, newPath, dependencyPath, metadataPath, reportPath] := args
    | throw <| IO.userError "Expected baseline, candidate, dependencies, metadata, report"
  let json ← match Json.parse (← IO.FS.readFile metadataPath) with
    | .ok j => pure j | .error e => throw <| IO.userError e
  let mods ← match json.getObjValAs? (Array String) "local_modules" with
    | .ok xs => pure xs | .error e => throw <| IO.userError e
  let sysroot ← findSysroot
  unless mods.size == 1199 do
    throw <| IO.userError "Expected the complete 1199-module inventory"
  for dir in [oldPath, newPath] do
    for m in mods do
      let path := System.FilePath.mk dir / (m.replace "." "/" ++ ".olean")
      unless ← path.pathExists do throw <| IO.userError s!"Missing proof object: {path}"
  searchPathRef.set [oldPath, dependencyPath, sysroot / "lib/lean"]
  let old ← importModules #[{module := `GoalRoot}] {}
  searchPathRef.set [newPath, dependencyPath, sysroot / "lib/lean"]
  let current ← importModules #[{module := `GoalRoot}] {}
  let localModules := old.header.modules.map fun m => mods.contains m.module.toString
  let work : MetaM Json := do
    let mut count := 0
    let mut bodies := 0
    let mut reduced := 0
    for (name, before) in old.constants.toList do
      if name.isInternal then continue
      let some idx := old.getModuleIdxFor? name | continue
      unless localModules[idx.toNat]! do continue
      let some after := current.find? name | throwError "Missing declaration {name}"
      unless kind before == kind after && before.levelParams == after.levelParams do
        throwError "Kind or universe parameters changed: {name}"
      if before.type != after.type then
        unless ← isDefEq before.type after.type do throwError "Type changed: {name}"
        reduced := reduced + 1
      if let .defnInfo b := before then
        let .defnInfo a := after | throwError "Definition changed kind: {name}"
        if b.value != a.value then
          unless ← isDefEq b.value a.value do throwError "Definition body changed: {name}"
        bodies := bodies + 1
      count := count + 1
    unless count > 0 do throwError "No original declarations found"
    return Json.mkObj [("baseline_objects", toJson oldPath),
      ("candidate_objects", toJson newPath), ("proof_modules", toJson mods.size),
      ("passed", toJson true), ("named_declarations", toJson count),
      ("definition_bodies", toJson bodies), ("types_requiring_reduction", toJson reduced)]
  let opts := ({} : Options).set `maxRecDepth (8192 : Nat) |>.set `maxHeartbeats (80000000 : Nat)
  let coreCtx : Core.Context := {
    fileName := "<preservation>"
    fileMap := FileMap.ofString ""
    options := opts
  }
  let result ← ((work.run').run' coreCtx {env := current}).toBaseIO
  match result with
  | .error e => throw <| IO.userError (← e.toMessageData.toString)
  | .ok report =>
    IO.FS.writeFile reportPath report.pretty
    IO.println report.pretty
    return 0
