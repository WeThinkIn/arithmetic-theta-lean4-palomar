import MarkedKatoValueDefinitionsR0159
import GammaZeroLocusR0159
import LaurentGammaTranslationR0064

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaMarkedKatoValuesR0159
open ArithmeticThetaLaurentNormR0064
open ArithmeticThetaNormFiniteR0063

private theorem cancel_translated_gamma {F : Type} [Field F]
    (q z g : F) (A P L T : ℤ) (n : ℕ)
    (hq : q ≠ 0) (hz : z ≠ 0) (hg : g ≠ 0) (hn : 1 ≤ n) :
    q ^ A * z ^ P * g ^ n / (z ^ (-L) * q ^ (-T) * g) =
      q ^ (A + T) * z ^ (P + L) * g ^ (n - 1) := by
  have hgpow : g ^ n * g⁻¹ = g ^ (n - 1) := by
    simpa only [pow_one] using (pow_sub₀ g hg hn).symm
  rw [zpow_neg, zpow_neg, div_eq_mul_inv, mul_inv_rev, mul_inv_rev,
    inv_inv, inv_inv, zpow_add₀ hq, zpow_add₀ hz]
  calc
    _ = (q ^ A * q ^ T) * (z ^ P * z ^ L) * (g ^ n * g⁻¹) := by ring
    _ = _ := by rw [hgpow]

/-- The raised Siegel identity with its exact scalar and integral exponent. -/
theorem raised_siegel_torsion_formula :
    ∀ (k : Type) [Field k] [CharZero k] (r N j : ℕ) (a : kˣ)
      (γ δ : LaurentSeries k), 0 < r → 0 < N → j < r → r ∣ N*j →
      (a : k)^N = 1 → (j ≠ 0 ∨ (a : k) ≠ 1) →
      IsGamma k r j (a : k) γ →
      IsGamma k r ((1+12*N)*j) ((a : k)^(1+12*N)) δ →
      literalValue k r (1+12*N) j (a : k) γ δ =
        siegelPower k r (1+12*N) j (a : k) γ := by
  intro k _ _ r N j a γ δ hr hN hj hdiv ha hnon hγ hδ
  let c := 1 + 12 * N
  let l := shift r c j
  have ha0 : (a : k) ≠ 0 := Units.ne_zero a
  have hac : (a : k) ^ c = (a : k) := by
    dsimp [c]
    rw [pow_add, pow_one, show 12 * N = N * 12 by omega, pow_mul, ha]
    simp
  have hshiftdiv : r ∣ (c - 1) * j := by
    dsimp [c]
    simpa only [Nat.add_sub_cancel_left, mul_assoc] using dvd_mul_of_dvd_right hdiv 12
  have hshift : r * l = (c - 1) * j := by
    exact Nat.mul_div_cancel' hshiftdiv
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hindex : c * j = j + r * l := by
    rw [hshift, Nat.sub_mul, one_mul]
    have : j ≤ c * j := by nlinarith
    omega
  have hδ' : IsGamma k r (j + r * l) (a : k) δ := by
    change IsGamma k r (c * j) ((a : k) ^ c) δ at hδ
    simpa only [← hindex, hac] using hδ
  have htrans := gamma_translation k r j l (a : k) hr hj ha0 γ δ hγ hδ'
  have hγ0 : γ ≠ 0 := by
    intro hzero
    obtain ⟨hd, ha1⟩ := (gamma_zero_locus k r j (a : k) γ hr ha0 hγ).mp hzero
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hd hj
    rcases hnon with h | h
    · exact h hj0
    · exact h ha1
  have ht : t k ≠ 0 := by simp [t]
  have hca : (-HahnSeries.C (a : k) : LaurentSeries k) ≠ 0 := by
    simp [HahnSeries.C_apply, ha0]
  have hz : (-(HahnSeries.C (a : k) * t k ^ j) : LaurentSeries k) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mp hca) (pow_ne_zero _ ht))
  change literalValue k r c j (a : k) γ δ = siegelPower k r c j (a : k) γ
  unfold literalValue
  rw [htrans, cancel_translated_gamma _ _ _ _ _ _ _ _ (pow_ne_zero _ ht) hz hγ0
    (by nlinarith : 1 ≤ c ^ 2)]
  have hq (e : ℤ) : (t k ^ r) ^ e = t k ^ ((r : ℤ) * e) := by
    rw [← zpow_natCast, ← zpow_mul]
  have hzpow (e : ℤ) : (-(HahnSeries.C (a : k) * t k ^ j)) ^ e =
      (-HahnSeries.C (a : k)) ^ e * t k ^ ((j : ℤ) * e) := by
    rw [← neg_mul, mul_zpow, ← zpow_natCast, ← zpow_mul]
  rw [hq, hzpow]
  unfold siegelPower
  change _ = (-HahnSeries.C (a : k)) ^ (p c + (l : ℤ)) *
    t k ^ ((r : ℤ) * (K c / 12) + (j : ℤ) * p c + (j : ℤ) * l +
      (r : ℤ) * ((l : ℤ) * ((l : ℤ) - 1) / 2)) * γ ^ (c ^ 2 - 1)
  rw [show (r : ℤ) * (K c / 12) + (j : ℤ) * p c + (j : ℤ) * l +
      (r : ℤ) * ((l : ℤ) * ((l : ℤ) - 1) / 2) =
      (r : ℤ) * (K c / 12 + triangle l) + (j : ℤ) * (p c + (l : ℤ)) by
        unfold triangle; ring, zpow_add₀ ht]
  ring

end ArithmeticThetaMarkedKatoValuesR0159
