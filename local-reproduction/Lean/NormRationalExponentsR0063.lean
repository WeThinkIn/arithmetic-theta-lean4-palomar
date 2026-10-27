import NormWeightedSumR0062

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormFiniteR0063

theorem rational_exponents :
    ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d →
      (((d : ℚ) - 1) * (-(c : ℚ) * ((c : ℚ) - 1) / 2) +
          (c : ℚ) * ArithmeticThetaNormQuotientsR0062.quotientSum c d = 0) ∧
      ((((d : ℚ) ^ 2 - 1) * ((c : ℚ) ^ 2 - 1) / 12 +
          (-(c : ℚ) * ((c : ℚ) - 1) / 2) * (d : ℚ) * ((d : ℚ) - 1) / 2 +
          ArithmeticThetaNormQuotientsR0062.weightedSum c d = 0) ∧
       (((d : ℚ) ^ 2 - 1) * (-(c : ℚ) * ((c : ℚ) - 1) / 2) +
          ArithmeticThetaNormQuotientsR0062.quotientSum c d =
            ((c : ℚ) - 1) * ((d : ℚ) - 1) *
              (1 - (c : ℚ) * ((d : ℚ) + 1)) / 2)) := by
  intro c d hc hd hcop
  rw [ArithmeticThetaNormQuotientsR0062.quotient_sum c d hc hd hcop,
      ArithmeticThetaNormQuotientsR0062.weighted_sum c d hc hd hcop]
  constructor
  · ring
  constructor
  · ring
  · ring

end ArithmeticThetaNormFiniteR0063
