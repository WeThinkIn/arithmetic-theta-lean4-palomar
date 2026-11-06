module
import all Challenge
import Lean
open Lean Elab Command
run_cmd do
  let targets : List Name := [``WeierstrassProjModel.span_polynomial_isHomogeneousCR, ``HomogeneousIdealQuotientGrading.preDecompose_of_mem, ``WeierstrassProjModel.kwYEvalRingHom_comp_algebraMap, ``HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff, ``HomogeneousIdealQuotientGrading.quotDecompose_mk, ``WeierstrassProjModel.kwYEvalRingHom_mk_X1, ``ProjWeierstrassCubicPrime.isHomogeneous_polynomial, ``HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_preDecompose, ``HomogeneousIdealQuotientGrading.gradedMonoidOfImages, ``HomogeneousIdealQuotientGrading.preDecompose_eq_zero_of_mem, ``HomogeneousIdealQuotientGrading.pieceHom_coe, ``HomogeneousIdealQuotientGrading.coeAddMonoidHom_map_pieceHom, ``WeierstrassProjModel.kwYChartEval_section, ``ArithmeticThetaPalomarComponent485.componentIsOpen, ``ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_isIso, ``ArithmeticThetaComponentDegreeR0184.componentIntegral, ``ArithmeticThetaComponentDegreeR0184.componentLocallyNoetherian, ``ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor, ``ArithmeticThetaSectionCompletion.normal_stalk_dvr, ``ArithmeticThetaGeometricPrerequisites.divisorPresheaf_isSheaf, ``ArithmeticThetaPalomarHalf505.compactAlphaCanonicalHalfLine]
  let mut rows : Array Json := #[]
  for name in targets do
    let some r ← findDeclarationRanges? name | throwError "Missing target range {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)])
  logInfo (Json.compress (toJson rows))
