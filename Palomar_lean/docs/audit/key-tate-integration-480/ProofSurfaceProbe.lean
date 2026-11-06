module
import all Challenge
import Lean
open Lean Elab Command
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Challenge | throwError "Missing Challenge"
  let mut rows : Array Json := #[]
  for name in env.header.moduleData[idx]!.constNames do
    let some ci := env.find? name | continue
    let isProof ← liftTermElabM do Lean.Meta.isProp ci.type
    let range ← findDeclarationRanges? name
    rows := rows.push (Json.mkObj [
      ("name",toJson name.toString), ("proof",toJson isProof),
      ("start",toJson (range.map (·.range.pos.line))),
      ("start_column",toJson (range.map (·.range.pos.column))),
      ("end",toJson (range.map (·.range.endPos.line))),
      ("end_column",toJson (range.map (·.range.endPos.column)))])
  logInfo (Json.compress (toJson rows))
