module
public import Challenge
public meta import Lean
#print axioms WeierstrassProjModel.RelativeGroupLaw.schemeNsmul
#print axioms ArithmeticThetaGeometricNormR0150.IsFieldMap
#print axioms ArithmeticThetaGeometricNormR0150.fieldNorm
#print axioms ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction
#print axioms ArithmeticThetaRelativeKatoR0169.GenericComparison
#print axioms ArithmeticThetaRelativeKatoR0169.IsRelativeKato
#print axioms ArithmeticThetaPalomarNormalKato378.FiveNormalized
#print axioms ArithmeticThetaTensorPower.tensorPower
#print axioms ArithmeticThetaTensorPower.tensorPowerSection
#print axioms ArithmeticThetaPalomarDifferential365.relativeD
#print axioms ArithmeticThetaPalomarNormalInitial381.Hodge
#print axioms ArithmeticThetaPalomarNormalInitial381.localPower
#print axioms ArithmeticThetaPalomarNormalInitial381.FiveFrame
#print axioms ArithmeticThetaPalomarNormalInitial381.FiveInitial
#print axioms ArithmeticThetaPalomarNormalInitial381.FiveSpecification
#print axioms ArithmeticThetaArbitraryDiscriminantR0243.Comparison
#print axioms ArithmeticThetaArbitraryDiscriminantR0243.NormalModel
#print axioms ArithmeticThetaSchemeDiscriminantR0244.Comparison
#print axioms ArithmeticThetaPalomarIdentity357.CotangentCompatible
#print axioms ArithmeticThetaPalomarCanonicalTensor382.Compatible
#print axioms ArithmeticThetaPalomarSchemePower383.Compatible
#print axioms ArithmeticThetaPalomarFullScheme385.AffineLineCompatible
#print axioms ArithmeticThetaPalomarFullScheme385.AffinePowerCompatible
meta section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let projectModules := (← IO.FS.readFile "/home/Palomar/workspace/arithmetic-theta/evidence/ambient-roots-package-355/project-modules.txt").splitOn "\n"
  let names := env.header.modules.toList.map (fun m => m.module.toString)
  let projectImports := names.filter projectModules.contains
  unless projectImports.isEmpty do throwError "Unexpected project imports {projectImports}"
  logInfo (Json.compress (Json.mkObj [("project_imports", toJson projectImports), ("imported_module_count", toJson names.length)]))
