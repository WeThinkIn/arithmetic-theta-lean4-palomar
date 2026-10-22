module

public import LaurentPoweredNormR0064
public import LaurentPreimageMonomialsR0064
public import NormScalarCorrectionR0063

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064
open ArithmeticThetaNormFiniteR0063

private theorem fn_scalar_identity {F : Type} [Field F] (c d : ℕ)
    (v q : F) (hv : v ≠ 0) (hq : q ≠ 0) :
    (q ^ (K c / 12)) ^ (d ^ 2) *
        ((-1 : F) ^ (d ^ 2) * v ^ d * q ^ triangle d) ^ p c /
        ((-1 : F) ^ (-S c d) * v ^ (-(c : ℤ) * S c d) * q ^ (-E c d)) =
      correction c d v q * (q ^ (K c / 12) * (-v) ^ p c) := by
  have hn : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [show -(c : ℤ) * S c d = -((c : ℤ) * S c d) by ring]
  rw [show -v = (-1 : F) * v by ring]
  simp only [correction, signExponent, zExponent, qExponent, mul_zpow,
    ← zpow_natCast, ← zpow_mul, Nat.cast_pow, sub_mul,
    zpow_add₀ hn, zpow_add₀ hv, zpow_add₀ hq,
    zpow_sub₀ hn, zpow_sub₀ hv, zpow_sub₀ hq, one_mul,
    zpow_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp
  ring

/-- The norm of the constructed literal Laurent gamma expression. -/
theorem formal_f_norm : ∀ (K : Type) [Field K] [CharZero K]
    (c d : ℕ) (ζ : K), 1 < c → Nat.Coprime c 6 → 0 < d →
    Nat.Coprime c d → IsPrimitiveRoot ζ d →
    ∃ (G H : Fin d → Fin d → Series K) (b e : Series K),
      (∀ i j : Fin d, IsGamma (Coeff K) d i.val (a K ζ j.val 1) (G i j)) ∧
      (∀ i j : Fin d, IsGamma (Coeff K) d (c * i.val) (a K ζ j.val c) (H i j)) ∧
      IsGamma (Coeff K) d 0 (w K ^ d) b ∧
      IsGamma (Coeff K) d 0 (w K ^ (c * d)) e ∧
      (∀ i j : Fin d, G i j ≠ 0 ∧ H i j ≠ 0) ∧ b ≠ 0 ∧ e ≠ 0 ∧
      (∏ i : Fin d, ∏ j : Fin d,
        fValue K c d (point K ζ i.val j.val) (G i j) (H i j)) =
        fValue K c d (z K d) b e := by
  intro K _ _ c d ζ hc hc6 hd hcop hζ
  let : CharZero (Coeff K) := charZero_of_injective_ringHom
    ((algebraMap (LaurentPolynomial K) (Coeff K)).comp LaurentPolynomial.C).injective
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hn := coefficient_nonzero K ζ hζ0
  have hc0 : 0 < c := by omega
  have hcd0 : 0 < c * d := Nat.mul_pos hc0 hd
  have hexG (i j : Fin d) : ∃ g : Series K,
      IsGamma (Coeff K) d i.val (a K ζ j.val 1) g :=
    (gamma_exists_unique (Coeff K) d i.val (a K ζ j.val 1) hd
      (hn.1 j.val 1 (by omega)).1).exists
  have hexH (i j : Fin d) : ∃ h : Series K,
      IsGamma (Coeff K) d (c * i.val) (a K ζ j.val c) h :=
    (gamma_exists_unique (Coeff K) d (c * i.val) (a K ζ j.val c) hd
      (hn.1 j.val c hc0).1).exists
  choose G hG using hexG
  choose H hH using hexH
  obtain ⟨b, hb, _⟩ := gamma_exists_unique (Coeff K) d 0 (w K ^ d) hd
    (hn.2.1 d hd).1
  obtain ⟨e, he, _⟩ := gamma_exists_unique (Coeff K) d 0 (w K ^ (c * d)) hd
    (hn.2.1 (c * d) hcd0).1
  have hb0 : b ≠ 0 := gamma_nonzero (Coeff K) d 0 (w K ^ d) hd
    (hn.2.1 d hd).1 (hn.2.1 d hd).2 b hb
  have he0 : e ≠ 0 := gamma_nonzero (Coeff K) d 0 (w K ^ (c * d)) hd
    (hn.2.1 (c * d) hcd0).1 (hn.2.1 (c * d) hcd0).2 e he
  refine ⟨G, H, b, e, hG, hH, hb, he, ?_, hb0, he0, ?_⟩
  · intro i j
    exact ⟨gamma_nonzero (Coeff K) d i.val (a K ζ j.val 1) hd
      (hn.1 j.val 1 (by omega)).1 (hn.1 j.val 1 (by omega)).2 (G i j) (hG i j),
      gamma_nonzero (Coeff K) d (c * i.val) (a K ζ j.val c) hd
      (hn.1 j.val c hc0).1 (hn.1 j.val c hc0).2 (H i j) (hH i j)⟩
  have hroot : IsPrimitiveRoot (scalar K ζ) d := hζ.map_of_injective
    ((algebraMap (LaurentPolynomial K) (Coeff K)).comp LaurentPolynomial.C).injective
  have hGprod : (∏ i : Fin d, ∏ j : Fin d, G i j) = b := by
    apply transport_unpowered_norm (Coeff K) d (scalar K ζ) (w K) hd hroot
      (by simpa using (hn.2.1 1 (by omega)).1) G b
    · intro i j
      simpa only [a, one_mul, pow_one] using hG i j
    · exact hb
  have hHprod := powered_gamma_norm K c d ζ hc hd hcop hζ H e hH he
  have hpoint := preimage_monomial_product K d ζ hd hζ
  have hq := (hn.2.2.1 d).1
  have hz := (hn.2.2.1 d).2
  have hcorr := scalar_correction (Series K) c d hc hc6 hd hcop (z K d) (Q K d) hz hq
  have hs := fn_scalar_identity c d (z K d) (Q K d) hz hq
  rw [hcorr, one_mul] at hs
  unfold fValue
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_zpow, Finset.prod_pow]
  rw [hGprod, hHprod, hpoint]
  rw [← pow_mul, ← pow_two]
  calc
    _ = (((Q K d ^ (ArithmeticThetaNormFiniteR0063.K c / 12)) ^ (d ^ 2) *
        ((-1 : Series K) ^ (d ^ 2) * z K d ^ d * Q K d ^ triangle d) ^ p c /
        ((-1 : Series K) ^ (-S c d) * z K d ^ (-(c : ℤ) * S c d) *
          Q K d ^ (-E c d))) * (b ^ (c ^ 2) / e)) := by ring
    _ = _ := by rw [hs]; ring

end ArithmeticThetaLaurentNormR0064
