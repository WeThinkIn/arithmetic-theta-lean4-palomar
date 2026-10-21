module
public import Lake.Check.Compare
public import Lake.Check.Axioms
public import Lake.Check.Util
public import Lean
public section
open Lean
set_option maxRecDepth 16000

def names (j : Json) (key : String) : IO (Array Name) := do
  return (← IO.ofExcept (j.getObjValAs? (Array String) key)).map String.toName

partial def diff (a b : Expr) : String :=
  if a == b then "equal" else
  match a, b with
  | .app f x, .app g y => if f != g then diff f g else diff x y
  | .lam _ t v _, .lam _ t' v' _
  | .forallE _ t v _, .forallE _ t' v' _ => if t != t' then diff t t' else diff v v'
  | .letE _ t v b _, .letE _ t' v' b' _ => if t != t' then diff t t' else if v != v' then diff v v' else diff b b'
  | _, _ => s!"C={repr a} S={repr b}"

def inspect (cfg : Json) (challenge solution : LeanExport.ExportedEnv) : IO Json := do
  let targets := (← names cfg "theorem_names") ++ (← names cfg "permitted_axioms")
  let mut pending := targets
  let mut seen : Std.HashSet Name := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some si := solution.constMap[n]? | continue
    let target := targets.contains n
    if let some ci := challenge.constMap[n]? then
      if (!target && ci != si) || ci.type != si.type || ci.levelParams != si.levelParams then
        let bd := match ci.value? true, si.value? true with
          | some c, some s => diff c s
          | _, _ => "missing value"
        rows := rows.push <| Json.mkObj [("name",toJson n.toString),("target",toJson target),("type_equal",toJson (ci.type == si.type)),("type_diff",toJson (diff ci.type si.type)),("body_diff",toJson bd),("levels_equal",toJson (ci.levelParams == si.levelParams))]
    else
      rows := rows.push <| Json.mkObj [("name",toJson n.toString),("missing_challenge",toJson true)]
    if target then
      pending := pending ++ si.type.getUsedConstants
    else
      let refs : Array Name := ((Lake.Check.runForUsedConsts si (fun n => modify (fun (xs : Array Name) => xs.push n)) : StateM (Array Name) Unit).run #[]).2
      pending := pending ++ refs
  return Json.mkObj [("checked",toJson seen.size),("mismatches",toJson rows)]

def main (args : List String) : IO UInt32 := do
  let [primPath, solutionPath] := args | throw (IO.userError "args")
  let primJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile primPath)
  let prim := (← IO.ofExcept (fromJson? primJson : Except String (Array String))).map String.toName
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "SOLUTION_PARSED_READY"
  stdout.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.trimAscii.toString == "quit" then break
    let req ← IO.ofExcept <| Json.parse line
    let cfgPath ← IO.ofExcept <| req.getObjValAs? String "config"
    let challengePath ← IO.ofExcept <| req.getObjValAs? String "challenge"
    let resultPath ← IO.ofExcept <| req.getObjValAs? String "result"
    let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile cfgPath)
    let thms ← names cfg "theorem_names"
    let axioms ← names cfg "permitted_axioms"
    let defs := ((cfg.getObjValAs? (Array String) "definition_names").toOption.getD #[]).map String.toName
    let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
    let verdict := Lake.Check.compareAt challenge solution (thms ++ axioms) defs prim
    let axVerdict := Lake.Check.checkAxioms solution thms defs axioms
    let diagnostic ← inspect cfg challenge solution
    let result := Json.mkObj [("structural",toJson (toString verdict)),("axioms",toJson (toString axVerdict)),("diagnostic",diagnostic),("limitation",toJson "No kernel verdict")]
    IO.FS.writeFile resultPath (result.pretty ++ "\n")
    stdout.putStrLn s!"STRUCTURAL {toString verdict}; AXIOMS {toString axVerdict}; RESULT {resultPath}"
    stdout.flush
  return 0
