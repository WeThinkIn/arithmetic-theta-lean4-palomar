module
public import AlternationRecovery3
public import LiftTransportRecovery
public import SymmetryRecovery
public import GlobalMarkingRecovery
import all AlternationRecovery3
import all LiftTransportRecovery
import all SymmetryRecovery
import all GlobalMarkingRecovery
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
noncomputable section
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaTateSchemeMarkingR0263 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
namespace PalomarActualLifts1337
open PalomarAlternation1305
 theorem scalar (ht : PalomarLift1168.Transport.{0}) (hg : GenericDualAction)
    (hd : InducedDual) (hc : ChangeInversion) (hs : PalomarSquare1209.Square)
    (hf : PalomarSquareRecovery1230.Faithfulness) : PalomarGlobal1194.Scalar := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨a, ha, hu⟩ := PalomarLift1168.scalar_matches ht k V Q he _ Q.mapA
    (ScalarLift.scalar_square k V Q) (Q.canonicalA he hζ)
  refine ⟨a, ⟨ha, ?_⟩, fun b hb => hu b hb.1⟩
  intro ι hι
  exact PalomarSymmetry1236.scalar_symmetric hs hf k V Q he a ι hι
    (PalomarAlternation1314.matched_scalar_alternating hg hd hc k V Q he hζ a ha ι hι)
 theorem shift (ht : PalomarLift1168.Transport.{0}) (hg : GenericDualAction)
    (hd : InducedDual) (hc : ChangeInversion) (hs : PalomarSquare1209.Square)
    (hf : PalomarSquareRecovery1230.Faithfulness) : PalomarGlobal1194.Shift := by
  intro k _ _ m hm he V ζ hζ Q
  obtain ⟨a, ha, hu⟩ := PalomarLift1168.shift_matches ht k V Q he
  refine ⟨a, ⟨ha, ?_⟩, fun b hb => hu b hb.1⟩
  intro ι hi
  have halt := PalomarAlternation1314.alternating_of_matches hg hd hc k V Q he hζ a ha ι hi
  have hisq : ∀ v : Γ(thetaLine (family k V) m, ⊤),
      SectionAction.globalAct _ ι (SectionAction.globalAct _ ι v) = v := by
    obtain ⟨h, hh⟩ := hi.2
    exact SectionAction.globalAct_square _ h ι hh
  let hr := SchemeMidpointThetaLift.reflection_square (family k V) (pointY k V)
  refine ⟨hr, PalomarSquareRecovery1230.shift_square hs hf k V Q he _ hr _ ?_⟩
  intro v
  change Sections.act _ (compose (family k V) m _ _ a ι)
    (Sections.act _ (compose (family k V) m _ _ a ι) v) = v
  dsimp only [compose]
  rw [Sections.act_comp, Sections.act_comp]
  have hh := congrArg (SectionAction.globalAct _ ι)
    (halt (SectionAction.globalAct _ ι v))
  simp only [hisq] at hh
  simpa only [Sections.act, SectionAction.globalAct] using hh

end PalomarActualLifts1337
