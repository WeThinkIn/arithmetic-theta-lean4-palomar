module
public import GenericGlobalMarking
import all GenericGlobalMarking
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
namespace PalomarGlobal1360
theorem globalmarking : PalomarProjective969.GlobalMarking :=
  PalomarGlobal1346.recover
    (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.markedModel_exists)
    (@ArithmeticThetaTateSchemeMarkingR0263.ShiftLiftProof.existsUnique_transport.{0})
    (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.genericDual_globalAct)
    (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.inducedIdealLift_dual)
    (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.symmetric_change_inversion)
    PalomarSquare1209.square
    (@ArithmeticThetaTateSchemeMarkingR0263.ScalarLift.model_lift_ext)
    (@ArithmeticThetaTateSchemeMarkingR0263.TateSchemeInversionLift.normalized_of_fixed_section)
    (@ArithmeticThetaSchemeThetaMarkingR0259.scheme_theta_inversion.{0})
    (@ArithmeticThetaSchemeThetaMarkingR0259.scheme_midpoint_theta_lift.{0})
    (@ArithmeticThetaSchemeThetaNaturalityR0262.scheme_global_sign_alignment.{0})
end PalomarGlobal1360
