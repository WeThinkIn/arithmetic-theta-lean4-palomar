import RatioQuotientR0067
import RationalOrderUniqueR0066
import HeightOneDVRR0066

/-! The difference law for the concrete finite numerator-denominator orders. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067
open ArithmeticThetaLocalOrdersR0066

private lemma exactOrder_of_addVal (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (a : GenericChart k) (n : ℕ)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P)
      (algebraMap (GenericChart k) (Localization.AtPrime P) a) = n) :
    ExactOrder k P a n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  unfold ExactOrder
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  simp only [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow, h]
  simp
  exact_mod_cast Nat.lt_succ_self n

private lemma exactOrder_mul (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (a b : GenericChart k) (m n : ℕ)
    (ha : ExactOrder k P a m) (hb : ExactOrder k P b n) :
    ExactOrder k P (a * b) (m + n) := by
  apply exactOrder_of_addVal
  simp only [map_mul, IsDiscreteValuationRing.addVal_mul,
    exactOrder_addVal k P a m ha, exactOrder_addVal k P b n hb, Nat.cast_add]

private lemma exactOrder_ne_zero (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    (a : GenericChart k) (n : ℕ) (ha : ExactOrder k P a n) : a ≠ 0 := by
  intro h
  subst a
  exact ha.2 (by simp)

/-- Finite orders subtract under division in the actual chart fraction field. -/
theorem quotient_order :
    ∀ (k : Type u) [Field k] [CharZero k]
      (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k)) [P.IsPrime]
      (f g : ArithmeticThetaLocalOrdersR0066.FunctionField k) (m n : ℤ),
      P.height = 1 → HasOrder k P f m → HasOrder k P g n →
      HasOrder k P (ratio k f g) (m - n) := by
  intro k _ _ P _ f g m n hP hf hg
  let := height_one_dvr k P hP
  obtain ⟨a, b, na, nb, hb, hab, ha, hbo, hm⟩ := hf
  obtain ⟨c, d, nc, nd, hd, hcd, hc, hdo, hn⟩ := hg
  have hc0 : c ≠ 0 := exactOrder_ne_zero k P c nc hc
  have hmc : toFunctionField k c ≠ 0 := by
    exact fun h => hc0 ((IsFractionRing.injective (GenericChart k) (FunctionField k))
      (by simpa [toFunctionField] using h))
  have hg0 : g ≠ 0 := by
    intro h
    apply hmc
    simpa [h] using hcd.symm
  refine ⟨a * d, b * c, na + nd, nb + nc, mul_ne_zero hb hc0, ?_,
    exactOrder_mul k P a d na nd ha hdo,
    exactOrder_mul k P b c nb nc hbo hc, ?_⟩
  · unfold ratio
    rw [map_mul, map_mul, ← hcd]
    calc
      f / g * (toFunctionField k b * (g * toFunctionField k d)) =
          (f * toFunctionField k b) * toFunctionField k d := by field_simp [hg0]
      _ = toFunctionField k a * toFunctionField k d := by rw [hab]
  · push_cast
    omega
end ArithmeticThetaRatioRegularityR0067
