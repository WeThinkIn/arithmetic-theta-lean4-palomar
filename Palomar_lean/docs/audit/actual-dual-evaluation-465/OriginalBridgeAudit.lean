module
import all Solution
import Lean
open Lean Elab Command Meta
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
run_cmd liftTermElabM do
  let base := "/home/Palomar/workspace/arithmetic-theta/evidence/actual-dual-evaluation-465/Challenge"
  let parts ← readModuleDataParts #[⟨base ++ ".olean"⟩, ⟨base ++ ".olean.server"⟩, ⟨base ++ ".olean.private"⟩]
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut checked : Nat := 0
  for (data, _) in parts do
    for ci in data.constants do
      if seen.contains ci.name then continue
      seen := seen.insert ci.name
      -- Compiler-generated private proof names are module/context dependent.
      -- Their axioms are covered by ChallengeAudit; compare named declarations here.
      if (ci.name.toString.splitOn "._proof_").length > 1 then continue
      let some original := env.find? ci.name | throwError "Missing declaration {ci.name}"
      unless ci.levelParams == original.levelParams do throwError "Universe mismatch {ci.name}"
      unless (← isDefEq ci.type original.type) do throwError "Declaration type mismatch {ci.name}"
      let axs ← collectAxioms ci.name
      unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
        throwError "Unapproved original/Solution closure {ci.name}: {axs}"
      checked := checked + 1
  logInfo m!"NAMED_CHALLENGE_DECLARATION_TYPES_AND_STANDARD_SOLUTION_CLOSURES {checked}"

open CategoryTheory MonoidalCategory AlgebraicGeometry
universe u
example {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.invModule = (ihom I.module).obj (𝟙_ X.Modules) := rfl
example {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.invModuleSection = MonoidalClosed.curry' I.moduleι := rfl
#print axioms ArithmeticThetaPalomarDual465.globalSectionsEquiv_eq_original
#print axioms ArithmeticThetaPalomarDual465.evaluationSection_eq_original
