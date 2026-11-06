import ScaledTateCompletionNodeIdealPowerTransportR0049
import ScaledTateCompletionStageCompatibilityR0049
import ScaledTateNodeCompletion
import ScaledTateCompletionTargetIdealSeparated

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

open ArithmeticThetaScaledTateBridgeR0046

theorem completion_specialization_exists_and_filtered :
    ∀ (k : Type u) [Field k] [CharZero k] (r i : ℕ) (hr : 0 < r)
      (hi : i < r) (a : k) (ha : a ≠ 0),
      ∃ φ : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+* PowerSeries k,
        φ.comp (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) =
          nodeMap k r i hr hi a ha ∧
        ∀ (n : ℕ) (z : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r),
          z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k r n →
            φ z ∈ (targetIdeal k) ^ (r * n) := by
  intro k _ _ r i hr hi a ha
  let J : Ideal (PowerSeries k) := targetIdeal k
  letI : IsAdicComplete J (PowerSeries k) := by
    change IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries k)
    infer_instance
  let hcont : ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
      Ideal.comap (nodeMap k r i hr hi a ha) J :=
    node_ideal_weak_continuity k r i hr hi a ha
  let fam : (n : ℕ) →
      ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
        PowerSeries k ⧸ J ^ n :=
    fun n => compFamily k r i hr hi a ha hcont n
  have hfam : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (fam n) = fam m := by
    intro m n hmn
    exact stage_compatibility k r i m n hr hi a ha hcont hmn
  let φ : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+* PowerSeries k :=
    IsAdicComplete.liftRingHom J fam hfam
  have hagree : φ.comp (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r) =
      nodeMap k r i hr hi a ha := by
    apply RingHom.ext
    intro z
    apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk (J ^ n)
        (φ (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z)) =
      Ideal.Quotient.mk (J ^ n) (nodeMap k r i hr hi a ha z)
    rw [show φ (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z) =
        IsAdicComplete.liftRingHom J fam hfam
          (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z) by rfl]
    rw [IsAdicComplete.mk_liftRingHom]
    change (fam n) (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z) =
      Ideal.Quotient.mk (J ^ n) (nodeMap k r i hr hi a ha z)
    change (nodeMapMod k r i hr hi a ha hcont n)
        (AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) n
          (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r z)) = _
    simp [nodeMapMod, toCompleted, J]
  refine ⟨φ, hagree, ?_⟩
  intro n z hz
  have hgen : ArithmeticThetaScaledTateBridgeR0046.completedParameter k r ∈
      Ideal.comap φ (J ^ r) := by
    change φ (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r
      (ArithmeticThetaScaledTateBridgeR0046.t k r)) ∈ J ^ r
    rw [show φ (ArithmeticThetaScaledTateBridgeR0046.toCompleted k r
        (ArithmeticThetaScaledTateBridgeR0046.t k r)) =
        nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.t k r) by
      exact DFunLike.congr_fun hagree (ArithmeticThetaScaledTateBridgeR0046.t k r)]
    change nodeMap k r i hr hi a ha (ArithmeticThetaScaledTateBridgeR0046.t k r) ∈ J ^ r
    rw [(node_map_coordinates k r i hr hi a ha).1]
    change PowerSeries.X ^ r ∈ (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) ^ r
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hpow :
      (ArithmeticThetaScaledTateBridgeR0046.completedPower k r n) ≤
        Ideal.comap φ ((J ^ r) ^ n) := by
    rw [show ArithmeticThetaScaledTateBridgeR0046.completedPower k r n =
        (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.completedParameter k r}) ^ n by rfl]
    exact (pow_le_pow_left' (Ideal.span_le.2 (Set.singleton_subset_iff.2 hgen)) n).trans
      (Ideal.le_comap_pow φ n)
  have hz' : φ z ∈ (J ^ r) ^ n := hpow hz
  simpa [J, ← pow_mul] using hz'

end ArithmeticThetaScaledTateCompletionExtensionR0048
