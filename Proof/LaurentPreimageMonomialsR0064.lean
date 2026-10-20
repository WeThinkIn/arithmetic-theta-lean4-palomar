module

public import LaurentNormDefinitionsR0064

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064

private theorem monomial_triangle_sum (d : ℕ) :
    ArithmeticThetaNormFiniteR0063.triangle d = ((∑ i : Fin d, i.val : ℕ) : ℤ) := by
  have h := Finset.sum_range_id_mul_two d
  rw [← Fin.sum_univ_eq_sum_range] at h
  unfold ArithmeticThetaNormFiniteR0063.triangle
  cases d with
  | zero => simp
  | succ n =>
    have hh : ((∑ i : Fin (n + 1), i.val : ℕ) : ℤ) * 2 =
        (n + 1 : ℤ) * n := by exact_mod_cast h
    rw [Nat.cast_add, Nat.cast_one]
    ring_nf at hh ⊢
    omega

private theorem monomial_double_product {R : Type*} [CommRing R]
    (d : ℕ) (x y u : R) (hx : x ^ d = 1) :
    (∏ i : Fin d, ∏ j : Fin d, (-(x ^ j.val * y * u ^ i.val))) =
      (-1 : R) ^ (d ^ 2) * (y ^ d) ^ d *
        (u ^ d) ^ (∑ i : Fin d, i.val) := by
  simp only [Finset.prod_neg, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_pow]
  have hxpow (j : Fin d) : (x ^ j.val) ^ d = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hx, one_pow]
  have hupow (i : Fin d) : (u ^ i.val) ^ d = (u ^ d) ^ i.val := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [hxpow, Finset.prod_const_one, one_mul, hupow,
    Finset.prod_pow_eq_pow_sum, ← pow_mul, ← Finset.mul_sum]
  ring

theorem preimage_monomial_product :
    ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K),
      0 < d → IsPrimitiveRoot ζ d →
      (∏ i : Fin d, ∏ j : Fin d, (-point K ζ i.val j.val)) =
        (-1 : Series K) ^ (d ^ 2) * z K d ^ d *
          Q K d ^ ArithmeticThetaNormFiniteR0063.triangle d := by
  intro K _ _ d ζ hd hζ
  have hx : (HahnSeries.C (scalar K ζ) : Series K) ^ d = 1 := by
    rw [← map_pow]
    simp only [scalar, ← map_pow, hζ.pow_eq_one, map_one]
  have hp (i j : Fin d) : point K ζ i.val j.val =
      (HahnSeries.C (scalar K ζ) : Series K) ^ j.val *
        HahnSeries.C (w K) * t (Coeff K) ^ i.val := by
    simp [point, a, map_mul, map_pow]
  simp_rw [hp]
  rw [monomial_double_product d _ _ _ hx, monomial_triangle_sum, zpow_natCast]
  simp [z, Q, map_pow]

end ArithmeticThetaLaurentNormR0064
