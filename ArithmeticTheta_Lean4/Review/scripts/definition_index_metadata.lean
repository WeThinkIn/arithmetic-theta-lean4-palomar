import Lean

/-! Read declaration docstrings and source positions for the review index.
This is documentation tooling; it does not build or alter proof declarations. -/

open Lean

private def field {α : Type} [FromJson α] (j : Json) (name : String) : IO α :=
  match j.getObjValAs? α name with
  | .ok a => pure a
  | .error e => throw <| IO.userError e

def main (args : List String) : IO UInt32 := do
  let [configPath, outputPath] := args
    | throw <| IO.userError "Expected CONFIG.json OUTPUT.json"
  let config ← match Json.parse (← IO.FS.readFile configPath) with
    | .ok j => pure j
    | .error e => throw <| IO.userError e
  let paths : Array String ← field config "search_path"
  let imports : Array String ← field config "imports"
  let names : Array String ← field config "names"
  let sysroot ← findSysroot
  searchPathRef.set (paths.toList.map System.FilePath.mk ++ [sysroot / "lib/lean"])
  let env ← importModules (imports.map fun s => {module := s.toName}) {}
  let read : CoreM Json := do
    let mut entries := #[]
    for name in names do
      let n := name.toName
      let ci ← getConstInfo n
      let doc ← findDocString? env n (includeBuiltin := false)
      let range ← findDeclarationRanges? n
      entries := entries.push <| Json.mkObj [
        ("name", toJson name),
        ("docstring", toJson doc),
        ("line", toJson (range.map (·.selectionRange.pos.line))),
        ("end_line", toJson (range.map (·.range.endPos.line))),
        ("is_structure", toJson (getStructureInfo? env ci.name).isSome)]
    return Json.arr entries
  let ctx : Core.Context := {fileName := "<definition-index>", fileMap := FileMap.ofString ""}
  match ← (read.run' ctx {env}).toBaseIO with
  | .error e => throw <| IO.userError (← e.toMessageData.toString)
  | .ok result => IO.FS.writeFile outputPath result.pretty
  return 0
