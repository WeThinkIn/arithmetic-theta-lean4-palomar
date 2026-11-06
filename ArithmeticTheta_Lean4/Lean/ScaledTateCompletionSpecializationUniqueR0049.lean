import ScaledTateCompletionSpecializationExistsR0049

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

open ArithmeticThetaScaledTateBridgeR0046

theorem completion_specialization_unique :
    ∀ (k : Type u) [Field k] [CharZero k] (r i : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0)
      (φ ψ : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+* PowerSeries k),
      φ.comp (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) =
        nodeMap k r i hr hi a ha →
      ψ.comp (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) =
        nodeMap k r i hr hi a ha →
      (∀ (n : ℕ) (z : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r),
        z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k r n →
          φ z ∈ (targetIdeal k) ^ (r * n)) →
      (∀ (n : ℕ) (z : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r),
        z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k r n →
          ψ z ∈ (targetIdeal k) ^ (r * n)) → φ = ψ := by
  intro k _ _ r i hr hi a ha φ ψ hφ hψ hfφ hfψ
  obtain ⟨_, _, _, _, _, _, happrox⟩ := completion_reductions k r hr
  apply RingHom.ext
  intro z
  apply sub_eq_zero.mp
  apply target_ideal_separated k
  intro n
  obtain ⟨p, hp⟩ := happrox n z
  have hagree : φ (toCompleted k r (quotientMap k r p)) =
      ψ (toCompleted k r (quotientMap k r p)) :=
    (DFunLike.congr_fun hφ (quotientMap k r p)).trans
      (DFunLike.congr_fun hψ (quotientMap k r p)).symm
  have hdiff : φ z - ψ z ∈ (targetIdeal k) ^ (r * n) := by
    have hmem := (targetIdeal k ^ (r * n)).sub_mem (hfφ n _ hp) (hfψ n _ hp)
    simpa only [map_sub, hagree, sub_sub_sub_cancel_right] using hmem
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n hr) hdiff

end ArithmeticThetaScaledTateCompletionExtensionR0048
