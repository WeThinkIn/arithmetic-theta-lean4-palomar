module
public import Challenge
public meta import Lean
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names := [``ArithmeticThetaPalomarCoordinates377.algebraic_tate_coordinates,
    ``ArithmeticThetaPalomarCoordinates377.coordinate_exact_poles,
    ``ArithmeticThetaPalomarCoordinates377.algebraic_model_cubic,
    ``ArithmeticThetaPalomarCoordinates377.global_normalized_differential,
    ``ArithmeticThetaPalomarCoordinates377.NormalizedFrame]
  let mut rows := #[]
  for n in names do
    let some ci := env.find? n | throwError "missing declaration {n}"
    rows := rows.push (Json.mkObj [("name",toJson n.toString),
      ("type_repr",toJson (reprStr ci.type)),
      ("normalized_frame_value_repr",toJson (if n == ``ArithmeticThetaPalomarCoordinates377.NormalizedFrame then reprStr ci.value? else "not requested"))])
  logInfo (Json.compress (Json.mkObj [("types",toJson rows)]))
