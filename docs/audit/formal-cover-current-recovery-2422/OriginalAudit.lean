module
import all FormalCoverRecovery2418
import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
 let env ← getEnv
 let data ← IO.ofExcept <| Json.parse (← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/remaining-five-render-publication-2398/project/docs/SourceObligations.json")
 let rows ← IO.ofExcept data.getArr?
 let mut found : Array Json := #[]
 for row in rows do
  let id ← IO.ofExcept <| row.getObjValAs? String "id"
  if !(#["accepted-050"]).contains id then continue
  let original ← IO.ofExcept <| row.getObjValAs? String "declaration"
  let recovery := (match id with
   | "accepted-050" => "ArithmeticThetaFormalCoverRecovery2418.recover_original_050"
   | _ => "").toName
  let a ← getConstInfo recovery
  let b ← getConstInfo original.toName
  unless (← isDefEq a.type b.type) && a.levelParams == b.levelParams do throwError "Original type mismatch {id}"
  let axs ← collectAxioms recovery
  unless axs.all (fun n => #[`propext,`Classical.choice,`Quot.sound].contains n) do throwError "Unexpected axioms {id}"
  found := found.push <| Json.mkObj [("id",toJson id),("original",toJson original),("recovery",toJson recovery.toString),("type_definitionally_equal",toJson true),("raw_type_expression_equal",toJson (a.type == b.type)),("universes_equal",toJson true),("axioms",toJson (axs.map Name.toString))]
 unless found.size == 1 do throwError "Missing original endpoints"
 IO.FS.writeFile "/home/Palomar/workspace/arithmetic-theta/evidence/formal-cover-public-import-audit-2419/audit.json" (toJson found).pretty
 logInfo "ORIGINAL_ENDPOINTS_DEFINITIONAL_TYPE_UNIVERSE_AXIOM_PASS"
