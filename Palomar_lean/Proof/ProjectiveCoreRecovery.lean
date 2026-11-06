module
public import ProjectiveCoreBridge
@[expose] public section
namespace PalomarProjective956
theorem original_global_arithmetic_projective_ratios :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := recover_from_components global_theta_core PalomarProjective954.quotient_transfer
end PalomarProjective956
