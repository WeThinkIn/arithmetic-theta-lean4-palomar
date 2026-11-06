module
public import InducedSquareRecovery
import all InducedSquareRecovery
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaTateSchemeMarkingR0263 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaGenericEvaluationR0140
namespace PalomarAlternation1314
open PalomarAlternation1305
variable (hg : GenericDualAction) (hd : InducedDual) (hc : ChangeInversion)
variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
 (V : TateLevel k (2*m)) {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)
include hg hd hc in
lemma matched_scalar_alternating (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointX k V)))
    (ha : Matches k V Q he _ Q.mapA a (Q.canonicalA he hζ))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hι : NormalizedInversion (family k V) m ι)
    (v : Γ(thetaLine (family k V) m, ⊤)) :
    SectionAction.globalAct _ ι (SectionAction.globalAct _ a
      (SectionAction.globalAct _ ι (SectionAction.globalAct _ a v))) = v := by
  exact PalomarAlternation1305.Scalar.matched_scalar_alternating hg hd
    (PalomarInducedSquare1307.induced_square hg hd) hc k V Q he hζ a ha ι hι v
include hg hd hc in
lemma alternating_of_matches (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointY k V)))
    (ha : Matches k V Q he _ Q.mapB a (Q.canonicalB he))
    (ι : Lift (family k V) m (inverse (family k V)))
    (hi : NormalizedInversion (family k V) m ι) :
    ∀ v : Γ(thetaLine (family k V) m, ⊤),
      SectionAction.globalAct _ ι (SectionAction.globalAct _ a
        (SectionAction.globalAct _ ι (SectionAction.globalAct _ a v))) = v := by
  exact PalomarAlternation1305.Shift.alternating_of_matches hg hd
    (PalomarInducedSquare1307.induced_square hg hd) hc k V Q he hζ a ha ι hi
end PalomarAlternation1314
