import TatePartialXStabilization
import TatePartialYStabilization

namespace ArithmeticThetaTateBridges

/-- The coefficients of both literal normalized annular sums stabilize at the
    cutoff one greater than their degree. -/
theorem annular_stabilization {k : Type u} [Field k] [CharZero k]
    (d i : ℕ) (a : k) (ha : ArithmeticThetaTateSeries.Admissible d i a) :
    ∀ n N : ℕ, n + 1 ≤ N →
      PowerSeries.coeff n (ArithmeticThetaTateSeries.partialX d i a N) =
        PowerSeries.coeff n (ArithmeticThetaTateSeries.partialX d i a (n+1)) ∧
      PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a N) =
        PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a (n+1)) := by
  intro n N hN
  exact ⟨partial_x_stabilization d i a ha n N hN,
    partial_y_stabilization d i a ha n N hN⟩

end ArithmeticThetaTateBridges
