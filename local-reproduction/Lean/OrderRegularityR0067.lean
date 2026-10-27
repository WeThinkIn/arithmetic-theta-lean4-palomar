import HeightOneDVRR0066
import RationalOrderUniqueR0066

/-! Finite rational order and regularity on the actual generic completed chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRatioRegularityR0067
open ArithmeticThetaLocalOrdersR0066

/-- Finite ideal-power order is nonnegative precisely for a regular fraction. -/
theorem order_regularity :
    ∀ (k : Type u) [Field k] [CharZero k]
      (P : Ideal (ArithmeticThetaLocalOrdersR0066.GenericChart k)) [P.IsPrime]
      (f : ArithmeticThetaLocalOrdersR0066.FunctionField k) (m : ℤ),
      P.height = 1 → HasOrder k P f m → (RegularAt k P f ↔ 0 ≤ m) := by
  intro k _ _ P _ f m hP hf
  let := height_one_dvr k P hP
  obtain ⟨a, b, na, nb, hb, hab, ha, hbo, hm⟩ := hf
  let L := Localization.AtPrime P
  have hva := exactOrder_addVal k P a na ha
  have hvb := exactOrder_addVal k P b nb hbo
  change IsDiscreteValuationRing.addVal L (algebraMap (GenericChart k) L a) = na at hva
  change IsDiscreteValuationRing.addVal L (algebraMap (GenericChart k) L b) = nb at hvb
  constructor
  · rintro ⟨c, d, hd, hcd⟩
    have hcross : a * d = c * b := by
      apply IsFractionRing.injective (GenericChart k) (FunctionField k)
      change toFunctionField k (a * d) = toFunctionField k (c * b)
      rw [map_mul, map_mul, ← hab, ← hcd]
      ring
    have hvd : IsDiscreteValuationRing.addVal L (algebraMap (GenericChart k) L d) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
        (IsLocalization.map_units L (⟨d, hd⟩ : P.primeCompl))
    have hv := congrArg (fun x => IsDiscreteValuationRing.addVal L
      (algebraMap (GenericChart k) L x)) hcross
    simp only [map_mul, IsDiscreteValuationRing.addVal_mul, hva, hvb, hvd, add_zero] at hv
    have hle : (nb : ℕ∞) ≤ (na : ℕ∞) := by
      rw [hv]
      exact le_add_left le_rfl
    have hn : nb ≤ na := by exact_mod_cast hle
    omega
  · intro hnonneg
    have hn : nb ≤ na := by omega
    have hdiv : algebraMap (GenericChart k) L b ∣ algebraMap (GenericChart k) L a := by
      apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
      rw [hva, hvb]
      exact_mod_cast hn
    obtain ⟨z, hz⟩ := hdiv
    obtain ⟨⟨c, d⟩, hzd⟩ := IsLocalization.surj P.primeCompl z
    have hcross : a * (d : GenericChart k) = b * c := by
      apply IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
      simp only [map_mul]
      rw [hz, mul_assoc, hzd]
    refine ⟨c, d, d.property, ?_⟩
    have hbK : toFunctionField k b ≠ 0 := by
      exact fun h => hb (IsFractionRing.injective (GenericChart k) (FunctionField k)
        (by simpa [toFunctionField] using h))
    apply mul_right_cancel₀ hbK
    calc
      f * toFunctionField k (d : GenericChart k) * toFunctionField k b =
          (f * toFunctionField k b) * toFunctionField k (d : GenericChart k) := by ring
      _ = toFunctionField k (a * (d : GenericChart k)) := by rw [hab, map_mul]
      _ = toFunctionField k c * toFunctionField k b := by rw [hcross, map_mul, mul_comm]

end ArithmeticThetaRatioRegularityR0067
