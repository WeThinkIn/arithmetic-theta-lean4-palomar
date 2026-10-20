module

public import ScaledTateCompletionNodeMapCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

theorem node_ideal_strong_continuity :
    ∀ (k : Type u) [Field k] [CharZero k] (r i : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0),
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
        Ideal.comap (nodeMap k r i hr hi a ha) ((targetIdeal k) ^ r) := by
  intro k _ _ r i hr hi a ha
  change Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k r} ≤
    Ideal.comap (nodeMap k r i hr hi a ha) ((targetIdeal k) ^ r)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.t k r) ∈
    (targetIdeal k) ^ r
  rw [(node_map_coordinates k r i hr hi a ha).1]
  change PowerSeries.X ^ r ∈ (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) ^ r
  rw [Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

end ArithmeticThetaScaledTateCompletionExtensionR0048
