import LocalNormDefinitionsR0054

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaLocalNormR0054

open ArithmeticThetaAnnularTorsionPrereqR0053
open ArithmeticThetaScaledTateBridgeR0046

private lemma chart_xy (k : Type u) [Field k] [CharZero k] :
    cx k * cy k = tau k := by
  change ArithmeticThetaScaledAnnularR0050.cx k 1 *
    ArithmeticThetaScaledAnnularR0050.cy k 1 =
      ArithmeticThetaScaledAnnularR0050.tau k 1
  change toCompleted k 1 (x k 1) * toCompleted k 1 (y k 1) = _
  rw [← map_mul]
  have hxy : x k 1 * y k 1 = t k 1 := by
    apply sub_eq_zero.mp
    have hrel : quotientMap k 1 (relation k 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    change quotientMap k 1 (MvPolynomial.X 0) * quotientMap k 1 (MvPolynomial.X 1) -
      algebraMap (ArithmeticThetaScaledTateBridgeR0046.Base k)
        (ArithmeticThetaScaledTateBridgeR0046.Node k 1) (parameter k 1) = 0
    change quotientMap k 1 (MvPolynomial.X 0) * quotientMap k 1 (MvPolynomial.X 1) -
      quotientMap k 1 (MvPolynomial.C (parameter k 1)) = 0
    simpa [relation, quotientMap] using hrel
  rw [hxy]
  simp [ArithmeticThetaScaledAnnularR0050.tau, t, parameter,
    completedBaseMap]

theorem local_coordinate_unit :
    ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ),
      IsUnit (localZ k j) ∧
        localZ k j = tpower k (j : ℤ) * toGeneric k (cx k) := by
  intro k _ _ j
  have ht : IsUnit (toGeneric k (tau k)) :=
    IsLocalization.Away.algebraMap_isUnit (tau k)
  have hx : IsUnit (toGeneric k (cx k)) := by
    apply isUnit_of_mul_isUnit_left
    rw [← map_mul, chart_xy]
    exact ht
  have hz : localZ k j = toGeneric k (tau k) ^ j * toGeneric k (cx k) := by
    simp [localZ, chartCoordinate]
  have htp : tpower k (j : ℤ) = toGeneric k (tau k) ^ j := by
    have hparam : (parameterUnit k : GenericChart k) = toGeneric k (tau k) :=
      (IsLocalization.Away.algebraMap_isUnit (tau k)).unit_spec
    simpa only [tpower, zpow_natCast, Units.val_pow_eq_pow_val, hparam]
  constructor
  · rw [hz]
    exact (ht.pow j).mul hx
  · rw [hz, htp]

end ArithmeticThetaLocalNormR0054
