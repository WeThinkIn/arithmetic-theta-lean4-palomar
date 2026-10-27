import ActualUnaryPowerValuesR0160

/-! Geometric realization from the accepted arithmetic-parameter construction. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnaryKatoPowerR0160

/-- Equation (power) on a constructed model, with all geometric providers in the conclusion. -/
theorem unary_power_geometric_realization :
    ∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → ArithmeticThetaUnaryKatoPowerR0160.GeometricRealization k d m N := by
  intro k _ _ d m N hd hm hem hN heN hmN
  exact actual_unary_geometric_realization k d m N hd hm hem hN heN hmN

end ArithmeticThetaUnaryKatoPowerR0160

#print axioms ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization
