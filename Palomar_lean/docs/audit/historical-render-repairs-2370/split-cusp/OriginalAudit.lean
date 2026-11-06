module
import all SplitCuspSolution
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
 let env ← getEnv
 let data ← IO.ofExcept <| Json.parse (← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/historical-scope-review-metadata-2335/project/docs/SourceObligations.json")
 let rows ← IO.ofExcept data.getArr?
 let mut found : Array Json := #[]
 for row in rows do
  let id ← IO.ofExcept <| row.getObjValAs? String "id"
  if !(#["accepted-072"]).contains id then continue
  let original ← IO.ofExcept <| row.getObjValAs? String "declaration"
  let recovery := (match id with
   | "accepted-072" => "ArithmeticThetaPalomarComponent485.recover_original_072"
   | _ => "").toName
  let a ← getConstInfo recovery
  let b ← getConstInfo original.toName
  unless a.type == b.type && a.levelParams == b.levelParams do throwError "Original type mismatch {id}"
  let axs ← collectAxioms recovery
  unless axs.all (fun n => #[`propext,`Classical.choice,`Quot.sound].contains n) do throwError "Unexpected axioms {id}"
  found := found.push <| Json.mkObj [("id",toJson id),("original",toJson original),("recovery",toJson recovery.toString),("type_expression_equal",toJson true),("universes_equal",toJson true),("axioms",toJson (axs.map Name.toString))]
 unless found.size == 1 do throwError "Missing original endpoints"
 IO.FS.writeFile "/home/Palomar/workspace/arithmetic-theta/evidence/historical-thirteen-original-endpoint-audit-2356/split-cusp/audit.json" (toJson found).pretty
 logInfo "ORIGINAL_ENDPOINTS_EXACT_TYPE_UNIVERSE_AXIOM_PASS"
