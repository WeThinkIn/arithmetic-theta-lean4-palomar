module
public import AlternationRecovery
import all AlternationRecovery
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 32768
set_option maxHeartbeats 64000000
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open LocalTheta
namespace PalomarInducedSquare1307
open PalomarAlternation1305
theorem induced_square (hg : GenericDualAction) (hd : InducedDual) : InducedSquare := by
  intro k _ _ r hr T M s d hL Y E N c f g h e α hα φ
  let e' := inducedIdealLift k M s d hL E N c f g h e α
  let v := (ihomGlobalSectionsEquiv (genericPower k M s d)
    (𝟙_ (genericScheme k M).Modules)).symm φ
  have hv : ihomGlobalSectionsEquiv _ _ v = φ := AddEquiv.apply_symm_apply _ _
  have hh : SectionAction.globalAct f (dualLift f _ hL e'.symm)
      (SectionAction.globalAct f (dualLift f _ hL e'.symm) v) = v := by
    dsimp only [e']
    rw [hd k M s d hL E N c f g h e α]
    apply SectionAction.globalAct_square_changeLine
    exact SectionAction.globalAct_square_baseChanged_iso E.hom g f h α hα
  have hh' := congrArg (ihomGlobalSectionsEquiv _ _) hh
  erw [hg, hg, hv] at hh'
  exact hh'

end PalomarInducedSquare1307
