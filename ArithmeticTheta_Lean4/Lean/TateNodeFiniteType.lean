import TateNodeChartDefinitions

/-! Noetherianity and finite type for the literal algebraic node quotient. -/

set_option autoImplicit false
universe u

namespace ArithmeticThetaNodeCharts

/-- The two-variable polynomial quotient is Noetherian and is a finite-type
algebra over the power-series base, with its canonical quotient algebra action. -/
theorem node_noetherian_finite_type :
    ∀ (k : Type u) [Field k] [CharZero k],
      IsNoetherianRing (ArithmeticThetaNodeCharts.Node k) ∧
        Algebra.FiniteType (ArithmeticThetaNodeCharts.Base k)
          (ArithmeticThetaNodeCharts.Node k) := by
  intro k _ _
  constructor
  · infer_instance
  · infer_instance

end ArithmeticThetaNodeCharts
