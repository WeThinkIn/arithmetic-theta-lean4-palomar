import ScaledTateCompletionExtensionDefinitions

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

theorem node_map_coordinates :
    ∀ (k : Type u) [Field k] [CharZero k] (r i : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0),
      nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.t k r) =
        PowerSeries.X ^ r ∧
      nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.x k r) =
        PowerSeries.C a * PowerSeries.X ^ i ∧
      nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.y k r) =
        PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i) := by
  intro k _ _ r i hr hi a ha
  constructor
  · change nodeMap k r i hr hi a ha
        (ArithmeticThetaScaledTateBridgeR0046.quotientMap k r
          (MvPolynomial.C (PowerSeries.X ^ r))) = _
    simp [ArithmeticThetaScaledTateBridgeR0046.quotientMap, nodeMap, baseMap]
  constructor
  · simp [ArithmeticThetaScaledTateBridgeR0046.x,
      ArithmeticThetaScaledTateBridgeR0046.quotientMap, nodeMap, baseMap]
  · simp [ArithmeticThetaScaledTateBridgeR0046.y,
      ArithmeticThetaScaledTateBridgeR0046.quotientMap, nodeMap, baseMap]

end ArithmeticThetaScaledTateCompletionExtensionR0048
