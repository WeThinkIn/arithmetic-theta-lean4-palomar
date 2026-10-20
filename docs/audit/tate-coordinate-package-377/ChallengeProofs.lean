module
public import Challenge
public meta import Lean
meta section
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let names := [``ArithmeticThetaInfinitesimalPolygonR0129.specA._proof_1, ``ArithmeticThetaInfinitesimalPolygonR0129.specR._proof_1]
  let mut rows := #[]
  for n in names do
    let some ci := env.find? n | throwError "missing declaration {n}"
    let prop ← liftTermElabM (Meta.isProp ci.type)
    unless prop do throwError "not proof: {n}"
    rows := rows.push (Json.mkObj [("name",toJson n.toString),
      ("is_prop",toJson prop),("type_repr",toJson (reprStr ci.type)),
      ("value_repr",toJson (reprStr ci.value?))])
  logInfo (Json.compress (Json.mkObj [("proofs",toJson rows)]))
