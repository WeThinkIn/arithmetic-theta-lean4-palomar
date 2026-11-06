module
public import Mathlib
public import UnaryPowerGeometricRealizationR0160
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
theorem ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization :
∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → ArithmeticThetaUnaryKatoPowerR0160.GeometricRealization k d m N := by
  exact ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization
theorem ArithmeticThetaPalomarUnary489.recover_original_093 :
∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → ArithmeticThetaUnaryKatoPowerR0160.GeometricRealization k d m N := ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization
