module

public import LocalNormDefinitionsR0054

@[expose] public section

/-! Endpoint horizontal factors in the concrete completed node of thickness one. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

/-- For period exponent `2*c`, the two endpoint horizontal factors are the
actual completed-node equations `1-x` and `1-y`. -/
theorem gamma_endpoint_factors :
    ∀ (k : Type u) [Field k] [CharZero k] (c : ℕ), 1 < c →
      gammaHorizontal k (2*c) 0 = 1 - ArithmeticThetaAnnularTorsionPrereqR0053.cx k ∧
      gammaHorizontal k (2*c) (2*c-1) =
        1 - ArithmeticThetaAnnularTorsionPrereqR0053.cy k := by
  intro k _ _ c hc
  have hfirst : 1 ≠ 2 * c := by omega
  have hlast : 2 * c - 1 ≠ 0 := by omega
  have hsucc : 2 * c - 1 + 1 = 2 * c := by omega
  constructor
  · simp [gammaHorizontal, ArithmeticThetaScaledAnnularR0050.gammaHorizontal,
      ArithmeticThetaAnnularTorsionPrereqR0053.cx, hfirst]
  · simp [gammaHorizontal, ArithmeticThetaScaledAnnularR0050.gammaHorizontal,
      ArithmeticThetaAnnularTorsionPrereqR0053.cy, hlast, hsucc]

end ArithmeticThetaLocalNormR0054
