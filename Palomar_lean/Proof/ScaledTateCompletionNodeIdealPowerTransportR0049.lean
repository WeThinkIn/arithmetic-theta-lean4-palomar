module

public import ScaledTateCompletionNodeIdealContinuityR0049
public import ScaledTateCompletionExtensionDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

theorem node_ideal_power_transport :
    ∀ (k : Type u) [Field k] [CharZero k] (r i : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0)
      (hcont : ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
        Ideal.comap (nodeMap k r i hr hi a ha) ((targetIdeal k) ^ r))
      (n : ℕ) (z : ArithmeticThetaScaledTateBridgeR0046.Node k r),
      z ∈ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n →
        nodeMap k r i hr hi a ha z ∈ (targetIdeal k) ^ (r * n) := by
  intro k _ _ r i hr hi a ha hcont n z hz
  have hpow : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n ≤
      Ideal.comap (nodeMap k r i hr hi a ha) (((targetIdeal k) ^ r) ^ n) :=
    (pow_le_pow_left' hcont n).trans
      (Ideal.le_comap_pow (nodeMap k r i hr hi a ha) n)
  have hz' : nodeMap k r i hr hi a ha z ∈ ((targetIdeal k) ^ r) ^ n :=
    hpow hz
  simpa [← pow_mul] using hz'

end ArithmeticThetaScaledTateCompletionExtensionR0048
