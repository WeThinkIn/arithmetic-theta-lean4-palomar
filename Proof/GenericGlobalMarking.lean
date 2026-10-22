module
public import ActualLiftsRecovery
public import TateInversionRecovery
import all ActualLiftsRecovery
import all TateInversionRecovery
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 64000000
namespace PalomarGlobal1346
open PalomarAlternation1305 PalomarGlobal1194
theorem recover (hm : PalomarGlobal1194.Model) (ht : PalomarLift1168.Transport.{0})
    (hg : GenericDualAction) (hd : InducedDual) (hc : ChangeInversion)
    (hs : PalomarSquare1209.Square) (hf : PalomarSquareRecovery1230.Faithfulness)
    (hn : PalomarTateInversion1331.Normalization)
    (hi : PalomarGlobal1194.SchemeInversion.{0}) (hp : PalomarGlobal1194.Midpoint.{0}) (ha : PalomarGlobal1194.Alignment.{0}) :
    PalomarProjective969.GlobalMarking :=
  PalomarGlobal1194.recover hm
    (PalomarTateInversion1331.tate_inversion ht hg hn)
    (PalomarActualLifts1337.scalar ht hg hd hc hs hf)
    (PalomarActualLifts1337.shift ht hg hd hc hs hf)
    hi hp ha
end PalomarGlobal1346
