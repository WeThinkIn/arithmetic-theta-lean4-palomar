module

public import LaurentNormDefinitionsR0064

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064

private theorem nz_factor_normalize (F : Type) [Field F] (b : F) (k : ℤ) :
    HahnSeries.C b * HahnSeries.single k (1 : F) =
      (HahnSeries.single k b : LaurentSeries F) := by
  simp [HahnSeries.C_apply, HahnSeries.single_mul_single]

private theorem nz_factor (F : Type) [Field F] (b : F) (hb : b ≠ 1) (k : ℤ) :
    (1 - HahnSeries.C b * HahnSeries.single k (1 : F) : LaurentSeries F) ≠ 0 := by
  rw [nz_factor_normalize]
  intro h
  have h0 := congrArg (fun x : LaurentSeries F => x.coeff 0) h
  by_cases hk : k = 0
  · subst k
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_one,
      HahnSeries.coeff_single_same, HahnSeries.coeff_zero, ite_true] at h0
    exact hb (sub_eq_zero.mp h0).symm
  · simp [HahnSeries.coeff_sub, HahnSeries.coeff_one, Ne.symm hk] at h0

private theorem nz_factor_order (F : Type) [Field F] (b : F) (hb : b ≠ 1)
    (k : ℤ) (hk : 0 < k) :
    (1 - HahnSeries.C b * HahnSeries.single k (1 : F) : LaurentSeries F).order = 0 := by
  have hn := nz_factor F b hb k
  have ho : (1 - HahnSeries.C b * HahnSeries.single k (1 : F) : LaurentSeries F).orderTop = 0 := by
    rw [nz_factor_normalize, HahnSeries.orderTop_sub, HahnSeries.orderTop_one]
    rw [HahnSeries.orderTop_one]
    exact HahnSeries.lt_orderTop_single hk
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero hn]
  exact ho

private theorem nz_partial (F : Type) [Field F] (d m N : ℕ) (b : F)
    (hb : b ≠ 1) : Partial F d m b N ≠ 0 := by
  unfold Partial
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun l _ => nz_factor F b hb _)
  · exact Finset.prod_ne_zero_iff.mpr (fun l _ => nz_factor F b⁻¹ (by simpa using hb) _)

private theorem nz_partial_succ (F : Type) [Field F] (d m N : ℕ) (b : F) :
    Partial F d m b (N + 1) = Partial F d m b N *
      (1 - HahnSeries.C b * HahnSeries.single ((d : ℤ) * N + m) (1 : F)) *
      (1 - HahnSeries.C b⁻¹ * HahnSeries.single ((d : ℤ) * (N + 1) - m) (1 : F)) := by
  simp only [Partial, Finset.prod_range_succ]
  ring

private theorem nz_partial_order_stable (F : Type) [Field F] (d m : ℕ) (b : F)
    (hd : 0 < d) (hb : b ≠ 1) : ∀ N : ℕ, m + 1 ≤ N →
      (Partial F d m b N).order = (Partial F d m b (m + 1)).order := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hN' : (m : ℤ) + 1 ≤ N := by exact_mod_cast hN
    have hpos : 0 < (d : ℤ) * N + m := by nlinarith
    have hpos' : 0 < (d : ℤ) * (N + 1) - m := by nlinarith
    rw [nz_partial_succ,
      HahnSeries.order_mul (mul_ne_zero (nz_partial F d m N b hb) (nz_factor F b hb _))
        (nz_factor F b⁻¹ (by simpa using hb) _),
      HahnSeries.order_mul (nz_partial F d m N b hb) (nz_factor F b hb _),
      nz_factor_order F b hb _ hpos,
      nz_factor_order F b⁻¹ (by simpa using hb) _ hpos', add_zero, add_zero, ih]

/-- A stabilized literal Laurent gamma product cannot vanish when its scalar
parameter avoids zero and one, even when finitely many exponents are negative. -/
theorem gamma_nonzero : ∀ (F : Type) [Field F] (d m : ℕ) (a : F),
    0 < d → a ≠ 0 → a ≠ 1 → ∀ g : LaurentSeries F, IsGamma F d m a g → g ≠ 0 := by
  intro F _ d m a hd _ ha g hg hz
  let e := (Partial F d m a (m + 1)).order
  obtain ⟨N₀, hN₀⟩ := hg e
  let N := max N₀ (m + 1)
  have he := hN₀ N (le_max_left _ _) e le_rfl
  have ho := nz_partial_order_stable F d m a hd ha N (le_max_right _ _)
  have hn := HahnSeries.coeff_order_eq_zero.not.mpr (nz_partial F d m N a ha)
  apply hn
  rw [ho]
  simpa [e, hz] using he

private theorem nz_fraction_injective (K : Type) [Field K] :
    Function.Injective (algebraMap (LaurentPolynomial K) (Coeff K)) :=
  IsFractionRing.injective _ _

private theorem nz_scalar (K : Type) [Field K] (r : K) (hr : r ≠ 0) :
    scalar K r ≠ 0 := by
  unfold scalar
  rw [← map_zero (algebraMap (LaurentPolynomial K) (Coeff K))]
  apply (nz_fraction_injective K).ne
  intro h
  have he := congrArg (fun p : LaurentPolynomial K => p.coeff 0) h
  exact hr (by simpa using he)

private theorem nz_w (K : Type) [Field K] : w K ≠ 0 := by
  unfold w
  rw [← map_zero (algebraMap (LaurentPolynomial K) (Coeff K))]
  apply (nz_fraction_injective K).ne
  exact (LaurentPolynomial.isUnit_T 1).ne_zero

private theorem nz_monomial_ne_one (K : Type) [Field K] (r : K) (n : ℕ)
    (hn : 0 < n) : scalar K r * w K ^ n ≠ 1 := by
  intro h
  have hp : LaurentPolynomial.C r * LaurentPolynomial.T (n : ℤ) = 1 := by
    apply nz_fraction_injective K
    rw [← mul_one (n : ℤ), ← LaurentPolynomial.T_pow, map_mul, map_pow]
    simpa only [scalar, w, map_one] using h
  have he := congrArg (fun p : LaurentPolynomial K => p.coeff 0) hp
  have hn' : (n : ℤ) ≠ 0 := by omega
  rw [← LaurentPolynomial.single_eq_C_mul_T] at he
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hn', if_false,
    AddMonoidAlgebra.coeff_one_zero] at he
  exact zero_ne_one he

/-- The concrete Laurent-polynomial indeterminate and scalar inclusions supply
all nonvanishing hypotheses for the formal norm denominators. -/
theorem coefficient_nonzero : ∀ (K : Type) [Field K] (ζ : K), ζ ≠ 0 →
    (∀ (j c : ℕ), 0 < c → a K ζ j c ≠ 0 ∧ a K ζ j c ≠ 1) ∧
    (∀ d : ℕ, 0 < d → w K ^ d ≠ 0 ∧ w K ^ d ≠ 1) ∧
    (∀ d : ℕ, Q K d ≠ 0 ∧ z K d ≠ 0) ∧
    (∀ i j : ℕ, point K ζ i j ≠ 0) := by
  intro K _ ζ hζ
  have hs := nz_scalar K ζ hζ
  have hw := nz_w K
  have ht : t (Coeff K) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have ha0 : ∀ j c : ℕ, a K ζ j c ≠ 0 := fun j c =>
    mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hw)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j c hc
    refine ⟨ha0 j c, ?_⟩
    have hm := nz_monomial_ne_one K (ζ ^ (c * j)) c hc
    simpa [a, scalar, map_pow] using hm
  · intro d hd
    refine ⟨pow_ne_zero _ hw, ?_⟩
    simpa [scalar] using nz_monomial_ne_one K 1 d hd
  · intro d
    exact ⟨pow_ne_zero _ ht, HahnSeries.C_ne_zero (pow_ne_zero _ hw)⟩
  · intro i j
    exact mul_ne_zero (HahnSeries.C_ne_zero (ha0 j 1)) (pow_ne_zero _ ht)

end ArithmeticThetaLaurentNormR0064
