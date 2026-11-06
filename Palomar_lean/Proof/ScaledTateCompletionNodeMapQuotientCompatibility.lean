module

public import ScaledTateCompletionExtensionDefinitions

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

theorem node_map_quotient_compatibility :
    ∀ (k : Type u) [Field k] [CharZero k] (r i m n : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0) (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (targetIdeal k) hmn).comp
          (nodeMapQuot k r i hr hi a ha n) =
        nodeMapQuot k r i hr hi a ha m := by
  intro k _ _ r i m n hr hi a ha hmn
  apply RingHom.ext
  intro z
  simp only [nodeMapQuot, RingHom.coe_comp, Function.comp_apply,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

end ArithmeticThetaScaledTateCompletionExtensionR0048
