module
import all Challenge
import Lean
open Lean Elab Command
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Challenge | throwError "Missing Challenge"
  let mut stack := #[``ArithmeticThetaPalomarKeyTate478.phaseFreeKeyTateNormalization, ``ArithmeticThetaPalomarSchemeAlpha437.alphaExists, ``ArithmeticThetaPalomarGlobalFrame401.normalizedFrameExists, ``ArithmeticThetaPalomarGlobalFrame401.normalizedFrameExistsUnique]
  let mut seen : NameSet := {}
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    let some ni := env.getModuleIdxFor? n | continue
    if ni != idx then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    stack := stack ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then stack := stack ++ v.getUsedConstants
    if let .inductInfo v := ci then stack := stack ++ v.ctors.toArray
  let mut rows : Array Json := #[]
  for name in env.header.moduleData[idx]!.constNames do
    let range ← findDeclarationRanges? name
    rows := rows.push (Json.mkObj [
      ("name",toJson name.toString), ("needed",toJson (seen.contains name)),
      ("start",toJson (range.map (·.range.pos.line))),
      ("end",toJson (range.map (·.range.endPos.line)))])
  logInfo (Json.compress (toJson rows))
