module
import all Challenge
import Lean
open Lean Elab Command
run_cmd do
  let targets : List Name := [``ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization]
  let mut rows : Array Json := #[]
  for name in targets do
    let some r ← findDeclarationRanges? name | throwError "Missing target range {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)])
  logInfo (Json.compress (toJson rows))
