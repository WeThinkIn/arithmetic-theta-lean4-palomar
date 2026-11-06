module
public import ConcreteGlobalMarking
public import ConcreteTateRatios2
import all ConcreteGlobalMarking
import all ConcreteTateRatios2
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 64000000
open AlgebraicGeometry
namespace PalomarOriginal1413
theorem original087 :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := PalomarProjective969.recover_from_providers
  PalomarProjective969.testexists PalomarProjective969.geometry PalomarProjective969.pointedgroup
  PalomarGlobal1360.globalmarking PalomarProjective969.commutator PalomarProjective969.invariantline
  PalomarProjective969.orbit PalomarProjective969.intertwining PalomarProjective969.naturality
  PalomarRatios1411.tateratios PalomarProjective954.quotient_transfer
end PalomarOriginal1413
