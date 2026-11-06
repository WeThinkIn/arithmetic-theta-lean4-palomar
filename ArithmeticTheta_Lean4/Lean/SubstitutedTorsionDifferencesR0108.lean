import AllCuspHalfDefinitionsR0108

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaAllCuspR0108

private lemma constantCoeff_subst_eq {k : Type u} [Field k]
    (w f : PowerSeries k) (hw : PowerSeries.constantCoeff w = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst w f) = PowerSeries.constantCoeff f := by
  let ha := PowerSeries.HasSubst.of_constantCoeff_zero' hw
  have hz : PowerSeries.constantCoeff
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) = 0 := by simp
  have hs := PowerSeries.constantCoeff_subst_eq_zero hw
    (f - PowerSeries.C (PowerSeries.constantCoeff f)) hz
  rw [PowerSeries.subst_sub ha, PowerSeries.subst_C] at hs
  rw [map_sub] at hs
  simpa only [PowerSeries.constantCoeff_eq, MvPowerSeries.constantCoeff_C] using sub_eq_zero.mp hs

private lemma order_subst_eq {k : Type u} [Field k]
    (w f : PowerSeries k) (hw : PowerSeries.constantCoeff w = 0)
    (hf : f ≠ 0) :
    PowerSeries.order (PowerSeries.subst w f) =
      f.order * w.order := by
  let n := f.order.toNat
  have hn : (n : ENat) = f.order := PowerSeries.coe_toNat_order hf
  have hcoeff : PowerSeries.constantCoeff (PowerSeries.divXPowOrder f) ≠ 0 := by
    simpa [PowerSeries.constantCoeff_divXPowOrder] using PowerSeries.coeff_order hf
  have hunit : PowerSeries.order
      (PowerSeries.subst w (PowerSeries.divXPowOrder f)) = 0 := by
    apply (PowerSeries.order_eq_nat (n := 0)).2
    constructor
    · rw [PowerSeries.coeff_zero_eq_constantCoeff]
      rwa [constantCoeff_subst_eq w _ hw]
    · intro i hi; omega
  have ha : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero' hw
  calc
    PowerSeries.order (PowerSeries.subst w f) =
        PowerSeries.order (PowerSeries.subst w
          (PowerSeries.X ^ n * PowerSeries.divXPowOrder f)) := by
          exact congrArg (fun g : PowerSeries k => PowerSeries.order (PowerSeries.subst w g))
            (PowerSeries.X_pow_order_mul_divXPowOrder (f := f)).symm
    _ = PowerSeries.order (w ^ n * PowerSeries.subst w (PowerSeries.divXPowOrder f)) := by
          rw [PowerSeries.subst_mul ha, PowerSeries.subst_pow ha,
            PowerSeries.subst_X ha]
    _ = n • w.order := by rw [PowerSeries.order_mul, hunit, add_zero, PowerSeries.order_pow]
    _ = f.order * w.order := by simp [← hn, nsmul_eq_mul]

private lemma base_differences {k : Type u} [Field k] [CharZero k] :
    (ArithmeticThetaTateSeries.e₁ k - ArithmeticThetaTateSeries.e₂ k).order = 0 ∧
    (ArithmeticThetaTateSeries.e₁ k - ArithmeticThetaTateSeries.e₃ k).order = 0 ∧
    (ArithmeticThetaTateSeries.e₂ k - ArithmeticThetaTateSeries.e₃ k).order = 2 := by
  have ht := ArithmeticThetaTateSeries.marked_cusp_terms (k := k) 1 (by omega)
  have hv := ArithmeticThetaTateIdentities.marked_cusp_vanishing (k := k) 1 (by omega)
  have h12 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₁ k -
      ArithmeticThetaTateSeries.e₂ k) ≠ 0 := by
    rw [map_sub]
    have h1 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₁ k) = -(4:k)⁻¹ := by
      simpa [ArithmeticThetaTateSeries.e₁, PowerSeries.coeff_zero_eq_constantCoeff] using ht.1
    have h2 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₂ k) = 0 := by
      simpa [ArithmeticThetaTateSeries.e₂] using hv.1 0 (by omega)
    rw [h1, h2]
    norm_num
  have h13 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₁ k -
      ArithmeticThetaTateSeries.e₃ k) ≠ 0 := by
    rw [map_sub]
    have h1 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₁ k) = -(4:k)⁻¹ := by
      simpa [ArithmeticThetaTateSeries.e₁, PowerSeries.coeff_zero_eq_constantCoeff] using ht.1
    have h3 : PowerSeries.coeff 0 (ArithmeticThetaTateSeries.e₃ k) = 0 := by
      simpa [ArithmeticThetaTateSeries.e₃] using hv.2.1 0 (by omega)
    rw [h1, h3]
    norm_num
  constructor
  · exact (PowerSeries.order_eq_nat (n := 0)).2 ⟨h12, by simp⟩
  constructor
  · exact (PowerSeries.order_eq_nat (n := 0)).2 ⟨h13, by simp⟩
  · apply (PowerSeries.order_eq_nat (n := 2)).2
    constructor
    · have hlead : PowerSeries.coeff 2 (ArithmeticThetaTateSeries.e₂ k -
          ArithmeticThetaTateSeries.e₃ k) = 4 := by
        simpa [ArithmeticThetaTateSeries.e₂, ArithmeticThetaTateSeries.e₃,
          map_sub] using ht.2.2.2.2.2
      rw [hlead]
      norm_num
    · intro n hn
      simp only [ArithmeticThetaTateSeries.e₂, ArithmeticThetaTateSeries.e₃, map_sub]
      rw [hv.1 n hn, hv.2.1 n hn, sub_self]

private lemma base_order {k : Type u} [Field k] [CharZero k]
    (i j : Fin 3) (hij : i ≠ j) :
    PowerSeries.order
      ((if i = 0 then ArithmeticThetaTateSeries.e₁ k
        else if i = 1 then ArithmeticThetaTateSeries.e₂ k
        else ArithmeticThetaTateSeries.e₃ k) -
       (if j = 0 then ArithmeticThetaTateSeries.e₁ k
        else if j = 1 then ArithmeticThetaTateSeries.e₂ k
        else ArithmeticThetaTateSeries.e₃ k)) =
      if i = 0 ∨ j = 0 then 0 else 2 := by
  rcases base_differences (k := k) with ⟨h12, h13, h23⟩
  fin_cases i <;> fin_cases j <;>
    simp_all
  · simpa only [show ArithmeticThetaTateSeries.e₂ k - ArithmeticThetaTateSeries.e₁ k =
        -(ArithmeticThetaTateSeries.e₁ k - ArithmeticThetaTateSeries.e₂ k) by ring,
        PowerSeries.order_neg] using h12
  · simpa only [show ArithmeticThetaTateSeries.e₃ k - ArithmeticThetaTateSeries.e₁ k =
        -(ArithmeticThetaTateSeries.e₁ k - ArithmeticThetaTateSeries.e₃ k) by ring,
        PowerSeries.order_neg] using h13
  · simpa only [show ArithmeticThetaTateSeries.e₃ k - ArithmeticThetaTateSeries.e₂ k =
        -(ArithmeticThetaTateSeries.e₂ k - ArithmeticThetaTateSeries.e₃ k) by ring,
        PowerSeries.order_neg] using h23

theorem substituted_two_torsion_differences :
    ∀ (k : Type u) [Field k] [CharZero k] (w : PowerSeries k), w ≠ 0 →
      PowerSeries.constantCoeff w = 0 → ∀ i j : Fin 3, i ≠ j →
      (rootSeries k w i - rootSeries k w j ≠ 0) ∧
      (PowerSeries.order (rootSeries k w i - rootSeries k w j) =
        if i = 0 ∨ j = 0 then 0 else (2 : ENat) * w.order) := by
  intro k _ _ w hw hw0 i j hij
  let f : Fin 3 → PowerSeries k := fun a =>
    if a = 0 then ArithmeticThetaTateSeries.e₁ k
    else if a = 1 then ArithmeticThetaTateSeries.e₂ k
    else ArithmeticThetaTateSeries.e₃ k
  have ha : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero' hw0
  have hb : PowerSeries.order (f i - f j) = if i = 0 ∨ j = 0 then 0 else 2 :=
    base_order i j hij
  have hfg : f i - f j ≠ 0 := by
    intro h
    rw [h, PowerSeries.order_zero] at hb
    split_ifs at hb <;> simp at hb
  have hs : rootSeries k w i - rootSeries k w j =
      PowerSeries.subst w (f i - f j) := by
    simp only [rootSeries, f, PowerSeries.subst_sub ha]
  have ho : PowerSeries.order (rootSeries k w i - rootSeries k w j) =
      (if i = 0 ∨ j = 0 then 0 else 2) * w.order := by
    rw [hs, order_subst_eq w (f i - f j) hw0 hfg, hb]
  have hfinite : w.order < ⊤ := PowerSeries.order_finite_iff_ne_zero.mpr hw
  constructor
  · intro h
    have ht := (PowerSeries.order_eq_top).2 h
    rw [ho] at ht
    split_ifs at ht
    · simp at ht
    · have hm : (2 : ENat) * w.order < ⊤ :=
        by
          rw [← PowerSeries.coe_toNat_order hw]
          change ((2 : ℕ) : ENat) * (w.order.toNat : ENat) < ⊤
          rw [← ENat.natCast_mul]
          exact ENat.natCast_lt_top _
      exact (ne_of_lt hm) ht
  · simpa [ite_mul] using ho

end ArithmeticThetaAllCuspR0108
