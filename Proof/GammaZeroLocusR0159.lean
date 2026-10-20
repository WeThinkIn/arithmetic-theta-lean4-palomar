module

public import LaurentGammaNonzeroR0064

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaMarkedKatoValuesR0159
open ArithmeticThetaLaurentNormR0064

private theorem factor_ne_zero (F : Type) [Field F] (b : F) (e : ℤ)
    (he : e ≠ 0) :
    (1 - HahnSeries.C b * HahnSeries.single e (1 : F) : LaurentSeries F) ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries F => x.coeff 0) h
  simp [HahnSeries.C_apply, HahnSeries.single_mul_single, Ne.symm he] at h0

private theorem factor_order (F : Type) [Field F] (b : F) (e : ℤ)
    (he : 0 < e) :
    (1 - HahnSeries.C b * HahnSeries.single e (1 : F) : LaurentSeries F).order = 0 := by
  have hn := factor_ne_zero F b e (ne_of_gt he)
  have ho : (1 - HahnSeries.C b * HahnSeries.single e (1 : F) : LaurentSeries F).orderTop = 0 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
    rw [HahnSeries.orderTop_sub, HahnSeries.orderTop_one]
    rw [HahnSeries.orderTop_one]
    exact HahnSeries.lt_orderTop_single he
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero hn]
  exact ho

private theorem partial_ne_zero (F : Type) [Field F] (r m N : ℕ) (b : F)
    (hdiv : ¬ r ∣ m) : Partial F r m b N ≠ 0 := by
  have hm : m ≠ 0 := fun h => hdiv (h ▸ dvd_zero r)
  unfold Partial
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro l _
    apply factor_ne_zero
    have : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have : (0 : ℤ) < (r : ℤ) * l + m := by positivity
    omega
  · apply Finset.prod_ne_zero_iff.mpr
    intro l _
    apply factor_ne_zero
    intro he
    have he' : m = r * (l + 1) := by exact_mod_cast (sub_eq_zero.mp he).symm
    exact hdiv ⟨l + 1, he'⟩

private theorem partial_succ (F : Type) [Field F] (r m N : ℕ) (b : F) :
    Partial F r m b (N + 1) = Partial F r m b N *
      (1 - HahnSeries.C b * HahnSeries.single ((r : ℤ) * N + m) (1 : F)) *
      (1 - HahnSeries.C b⁻¹ * HahnSeries.single ((r : ℤ) * (N + 1) - m) (1 : F)) := by
  simp only [Partial, Finset.prod_range_succ]
  ring

private theorem partial_order_stable (F : Type) [Field F] (r m : ℕ) (b : F)
    (hr : 0 < r) (hdiv : ¬ r ∣ m) : ∀ N : ℕ, m + 1 ≤ N →
      (Partial F r m b N).order = (Partial F r m b (m + 1)).order := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
    have hN' : (m : ℤ) + 1 ≤ N := by exact_mod_cast hN
    have hp : 0 < (r : ℤ) * N + m := by nlinarith
    have hq : 0 < (r : ℤ) * (N + 1) - m := by nlinarith
    rw [partial_succ,
      HahnSeries.order_mul (mul_ne_zero (partial_ne_zero F r m N b hdiv)
        (factor_ne_zero F b _ (ne_of_gt hp))) (factor_ne_zero F b⁻¹ _ (ne_of_gt hq)),
      HahnSeries.order_mul (partial_ne_zero F r m N b hdiv)
        (factor_ne_zero F b _ (ne_of_gt hp)),
      factor_order F b _ hp, factor_order F b⁻¹ _ hq, add_zero, add_zero, ih]

private theorem gamma_ne_zero_of_not_dvd (F : Type) [Field F] (r m : ℕ) (b : F)
    (hr : 0 < r) (hdiv : ¬ r ∣ m) (g : LaurentSeries F)
    (hg : IsGamma F r m b g) : g ≠ 0 := by
  intro hz
  let e := (Partial F r m b (m + 1)).order
  obtain ⟨N₀, hN₀⟩ := hg e
  let N := max N₀ (m + 1)
  have he := hN₀ N (le_max_left _ _) e le_rfl
  have ho := partial_order_stable F r m b hr hdiv N (le_max_right _ _)
  have hn := HahnSeries.coeff_order_eq_zero.not.mpr (partial_ne_zero F r m N b hdiv)
  apply hn
  rw [ho]
  simpa [e, hz] using he

private theorem partial_zero_of_dvd (F : Type) [Field F] (r q N : ℕ)
    (hN : q + 1 ≤ N) : Partial F r (r * q) 1 N = 0 := by
  unfold Partial
  by_cases hq : q = 0
  · subst q
    have hp : (∏ l ∈ Finset.range N,
        (1 - HahnSeries.C (1 : F) * HahnSeries.single ((r : ℤ) * l + ↑(r * 0)) (1 : F))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (show 0 < N by omega))
      simp
    rw [hp, zero_mul]
  · have hp : (∏ l ∈ Finset.range N,
        (1 - HahnSeries.C (1 : F)⁻¹ * HahnSeries.single ((r : ℤ) * (l + 1) - ↑(r * q)) (1 : F))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (show q - 1 < N by omega))
      have he : (r : ℤ) * ((q - 1 : ℕ) + 1) - ↑(r * q) = 0 := by
        have hq' : (q - 1 : ℕ) + 1 = q := by omega
        have hqz : ((q - 1 : ℕ) : ℤ) + 1 = q := by exact_mod_cast hq'
        rw [hqz, Nat.cast_mul, sub_self]
      rw [he]
      simp
    rw [hp, mul_zero]

/-- The complete zero locus, including scalar one and exponent zero, of the
literal Laurent gamma product with uniform agreement below every cutoff. -/
theorem gamma_zero_locus : ∀ (k : Type) [Field k] (r m : ℕ) (a : k)
    (γ : LaurentSeries k), 0 < r → a ≠ 0 → IsGamma k r m a γ →
    (γ = 0 ↔ r ∣ m ∧ a = 1) := by
  intro k _ r m a γ hr ha hγ
  constructor
  · intro hz
    constructor
    · by_contra hdiv
      exact gamma_ne_zero_of_not_dvd k r m a hr hdiv γ hγ hz
    · by_contra ha1
      exact gamma_nonzero k r m a hr ha ha1 γ hγ hz
  · rintro ⟨⟨q, rfl⟩, rfl⟩
    ext e
    obtain ⟨N₀, hN₀⟩ := hγ e
    have he := hN₀ (max N₀ (q + 1)) (le_max_left _ _) e le_rfl
    rw [partial_zero_of_dvd k r q _ (le_max_right _ _)] at he
    exact he.symm

end ArithmeticThetaMarkedKatoValuesR0159
