import ScaledTateCompletionNodeIdealContinuityR0049
import ScaledTateCompletionNodeMapQuotientCompatibility

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

theorem node_ideal_weak_continuity (k : Type u) [Field k] [CharZero k]
    (r i : ℕ) (hr : 0 < r) (hi : i < r) (a : k) (ha : a ≠ 0) :
    ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
      Ideal.comap (nodeMap k r i hr hi a ha) (targetIdeal k) := by
  exact (node_ideal_strong_continuity k r i hr hi a ha).trans
    (Ideal.comap_mono (Ideal.pow_le_self (Nat.ne_of_gt hr)))

theorem stage_compatibility :
    ∀ (k : Type u) [Field k] [CharZero k] (r i m n : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0)
      (hcont : ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
        Ideal.comap (nodeMap k r i hr hi a ha) (targetIdeal k)) (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (targetIdeal k) hmn).comp
          (compFamily k r i hr hi a ha hcont n) =
        compFamily k r i hr hi a ha hcont m := by
  intro k _ _ r i m n hr hi a ha hcont hmn
  let I := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r
  let J := targetIdeal k
  have hmod :
      (Ideal.Quotient.factorPow J hmn).comp
          (nodeMapMod k r i hr hi a ha hcont n) =
        (nodeMapMod k r i hr hi a ha hcont m).comp
          (Ideal.Quotient.factorPow I hmn) := by
    apply RingHom.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [nodeMapMod, I, J, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.lift_mk]
  have heval (z : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r) :
      Ideal.Quotient.factorPow I hmn
          (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z := by
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I
      (ArithmeticThetaScaledTateBridgeR0046.Node k r) z
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    have hs := s.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
    rw [← neg_sub]
    exact neg_mem hs
  apply RingHom.ext
  intro z
  -- The quotient-map square and the inverse-limit equation give the result pointwise.
  calc
    ((Ideal.Quotient.factorPow J hmn).comp
        (compFamily k r i hr hi a ha hcont n)) z =
      ((Ideal.Quotient.factorPow J hmn).comp
        (nodeMapMod k r i hr hi a ha hcont n))
        (AdicCompletion.evalₐ I n z) := rfl
    _ = nodeMapMod k r i hr hi a ha hcont m
          (Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z)) :=
      congrArg (fun f => f (AdicCompletion.evalₐ I n z)) hmod
    _ = (compFamily k r i hr hi a ha hcont m) z := by
      rw [heval]
      rfl

end ArithmeticThetaScaledTateCompletionExtensionR0048
