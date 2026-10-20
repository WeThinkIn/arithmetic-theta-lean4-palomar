module
public import Solution
public meta import Lean
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if env.header.modules[idx]!.module != `Solution then continue
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} for {n}"
    checked := checked.push (Json.mkObj [("name",toJson n.toString),("axioms",toJson (axioms.map Name.toString))])
  logInfo (Json.compress (Json.mkObj [("checked_count",toJson checked.size),("checked",toJson checked)]))
