import Lake.Check.Compare
import Lake.Check.Axioms
import Lean
open Lean
set_option maxRecDepth 16000

def names (j : Json) (key : String) : IO (Array Name) := do
  return (← IO.ofExcept (j.getObjValAs? (Array String) key)).map String.toName

def main (args : List String) : IO UInt32 := do
  let [cfgPath, primPath, challengePath, solutionPath] := args
    | throw (IO.userError "usage: Precheck config primitives challenge-export solution-export")
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile cfgPath)
  let primJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile primPath)
  let prim := (← IO.ofExcept (fromJson? primJson : Except String (Array String))).map String.toName
  let thms ← names cfg "theorem_names"
  let axioms ← names cfg "permitted_axioms"
  let defs := ((cfg.getObjValAs? (Array String) "definition_names").toOption.getD #[]).map String.toName
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  IO.println "EXPORTS_PARSED"
  match Lake.Check.compareAt challenge solution (thms ++ axioms) defs prim with
  | .error e => IO.eprintln e; return 1
  | .ok () => IO.println "TRUSTED_STRUCTURAL_COMPARISON_PASS"
  match Lake.Check.checkAxioms solution thms defs axioms with
  | .error e => IO.eprintln e; return 1
  | .ok () => IO.println "TRUSTED_AXIOM_CLOSURE_PASS"
  IO.println "PRECHECK_ONLY: no kernel verdict"
  return 0
