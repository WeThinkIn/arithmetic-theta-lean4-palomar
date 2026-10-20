module

public import LaurentGammaExistenceR0064
public import LaurentGammaTranslationR0064
public import LaurentGammaNonzeroR0064

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaLaurentNormR0064

private theorem periodicity_algebra {F : Type} [Field F] (c : ℕ) (hc : Odd c)
    (q v b e : F) (hq : q ≠ 0) (hv : v ≠ 0) (he : e ≠ 0) (r p : ℤ) :
    q ^ r * (-(q * v)) ^ p * ((-v) ^ (-1 : ℤ) * b) ^ (c ^ 2) /
      ((-(v ^ c)) ^ (-(c : ℤ)) * q ^ p * e) =
    q ^ r * (-v) ^ p * b ^ (c ^ 2) / e := by
  have hn : -(v ^ c) = (-v) ^ c := (hc.neg_pow v).symm
  have hs : ((-v) ^ c) ^ (-(c : ℤ)) = ((-v)⁻¹) ^ (c ^ 2) := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, inv_pow]
    congr 1
    simp [pow_two]
  rw [hn, hs]
  have hneg : -(q*v) = q * (-v) := by ring
  rw [hneg, mul_zpow, mul_pow]
  simp only [zpow_neg_one]
  have hvinv : (-v)⁻¹ ≠ 0 := inv_ne_zero (neg_ne_zero.mpr hv)
  have hqp : q ^ p ≠ 0 := zpow_ne_zero _ hq
  have hden : (-v)⁻¹ ^ (c ^ 2) * q ^ p * e ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hvinv) hqp) he
  apply (div_eq_div_iff hden he).2
  ring

/-- Formal periodicity constructed from the literal gamma limits. -/
theorem formal_f_periodicity :
    ∀ (K : Type) [Field K] [CharZero K] (c d : ℕ),
      1 < c → Nat.Coprime c 6 → 0 < d →
      ∃ (b e bShift eShift : Series K),
        IsGamma (Coeff K) d 0 (w K) b ∧
        IsGamma (Coeff K) d 0 (w K ^ c) e ∧
        IsGamma (Coeff K) d d (w K) bShift ∧
        IsGamma (Coeff K) d (c * d) (w K ^ c) eShift ∧
        b ≠ 0 ∧ e ≠ 0 ∧ bShift ≠ 0 ∧ eShift ≠ 0 ∧
        fValue K c d (Q K d * z K 1) bShift eShift =
          fValue K c d (z K 1) b e := by
  intro K _ _ c d hc hc6 hd
  have hn := coefficient_nonzero K 1 one_ne_zero
  have hw : w K ≠ 0 ∧ w K ≠ 1 := by simpa using hn.2.1 1 (by omega)
  have hwc := hn.2.1 c (by omega)
  obtain ⟨b, hb, _⟩ := gamma_exists_unique (Coeff K) d 0 (w K) hd hw.1
  obtain ⟨e, he, _⟩ := gamma_exists_unique (Coeff K) d 0 (w K ^ c) hd hwc.1
  obtain ⟨bShift, hbShift, _⟩ := gamma_exists_unique (Coeff K) d d (w K) hd hw.1
  obtain ⟨eShift, heShift, _⟩ := gamma_exists_unique (Coeff K) d (c*d) (w K ^ c) hd hwc.1
  have hb0 := gamma_nonzero (Coeff K) d 0 (w K) hd hw.1 hw.2 b hb
  have he0 := gamma_nonzero (Coeff K) d 0 (w K^c) hd hwc.1 hwc.2 e he
  have hbs0 := gamma_nonzero (Coeff K) d d (w K) hd hw.1 hw.2 bShift hbShift
  have hes0 := gamma_nonzero (Coeff K) d (c*d) (w K^c) hd hwc.1 hwc.2 eShift heShift
  refine ⟨b, e, bShift, eShift, hb, he, hbShift, heShift, hb0, he0, hbs0, hes0, ?_⟩
  have hbs := gamma_translation (Coeff K) d 0 1 (w K) hd hd hw.1 b bShift hb
    (by simpa using hbShift)
  have hes := gamma_translation (Coeff K) d 0 c (w K^c) hd hd hwc.1 e eShift he
    (by simpa [Nat.mul_comm] using heShift)
  have hbs' : bShift = (-(z K 1)) ^ (-1 : ℤ) * b := by
    have ht0 : ArithmeticThetaNormFiniteR0063.triangle 1 = 0 := by
      norm_num [ArithmeticThetaNormFiniteR0063.triangle]
    simpa only [Nat.mul_one, Nat.add_zero, pow_zero, mul_one,
      ht0, neg_zero, zpow_zero, one_mul, z, pow_one,
      Int.cast_one, Nat.cast_one] using hbs
  have hes' : eShift = (-((z K 1)^c)) ^ (-(c : ℤ)) *
      Q K d ^ ArithmeticThetaNormFiniteR0063.p c * e := by
    simpa [z, Q, ArithmeticThetaNormFiniteR0063.p, map_pow] using hes
  have hodd : Odd c := Nat.coprime_two_right.mp
    (Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 6) hc6)
  rw [hbs', hes']
  exact periodicity_algebra c hodd (Q K d) (z K 1) b e
    (hn.2.2.1 d).1 (hn.2.2.1 1).2 he0 _ _

end ArithmeticThetaLaurentNormR0064
