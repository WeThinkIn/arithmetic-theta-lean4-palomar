module
public import Challenge
public meta import Lean
#print axioms ArithmeticThetaPalomarNormalized394.Normalized
#print axioms ArithmeticThetaArbitraryDiscriminantR0243.NormalModel
#print axioms ArithmeticThetaSchemeDiscriminantR0244.Comparison
#print axioms ArithmeticThetaSchemeLevelR0204.multiple
#print axioms ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal
#print axioms ArithmeticThetaGeometricNormR0150.affineNorm
#print axioms ArithmeticThetaGeometricNormR0150.AffineFree
#print axioms ArithmeticThetaPalomarAffineKato394.FromModel
#print axioms ArithmeticThetaPalomarAffineKato394.IsKatoUnit
#print axioms ArithmeticThetaPalomarSchemeKato394.multiplication
#print axioms ArithmeticThetaPalomarSchemeKato394.complement
#print axioms ArithmeticThetaPalomarSchemeKato394.UnitSection
#print axioms ArithmeticThetaPalomarSchemeKato394.HasCartierDivisor
#print axioms ArithmeticThetaPalomarSchemeNorm394.IsNormSection
#print axioms ArithmeticThetaPalomarSchemeNorm394.NormFamily
#print axioms ArithmeticThetaPalomarSchemeNorm394.IsNormFamily
#print axioms ArithmeticThetaPalomarSchemeNorm394.NormInvariant
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let projectModules := (← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/ambient-roots-package-355/project-modules.txt").splitOn "\n"
  let names := env.header.modules.toList.map (fun m => m.module.toString)
  let projectImports := names.filter projectModules.contains
  unless projectImports.isEmpty do throwError "Unexpected project imports {projectImports}"
  logInfo (Json.compress (Json.mkObj [("project_imports", toJson projectImports), ("imported_module_count", toJson names.length)]))
