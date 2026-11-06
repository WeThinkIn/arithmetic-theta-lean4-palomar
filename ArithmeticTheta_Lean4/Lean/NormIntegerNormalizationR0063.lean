import NormIntegerCastsR0063
import NormRationalExponentsR0063
import NormExponentAlgebra

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormFiniteR0063

private theorem sign_target_dvd (c d : ℕ) (hc : Nat.Coprime c 6) :
    (2 : ℤ) ∣ ((c : ℤ) - 1) * ((d : ℤ) - 1) *
      (1 - (c : ℤ) * ((d : ℤ) + 1)) := by
  have hcop2 : Nat.Coprime c 2 := Nat.Coprime.of_dvd_right (by norm_num) hc
  have hodd : Odd c := (Nat.coprime_two_right.mp hcop2)
  rcases hodd with ⟨k, hk⟩
  refine ⟨(k : ℤ) * ((d : ℤ) - 1) *
      (1 - (c : ℤ) * ((d : ℤ) + 1)), ?_⟩
  norm_num [hk]
  ring

private theorem cast_sign_target (c d : ℕ) (hc : Nat.Coprime c 6) :
    (((((c : ℤ) - 1) * ((d : ℤ) - 1) *
      (1 - (c : ℤ) * ((d : ℤ) + 1))) / 2 : ℤ) : ℚ) =
      ((c : ℚ) - 1) * ((d : ℚ) - 1) *
        (1 - (c : ℚ) * ((d : ℚ) + 1)) / 2 := by
  rw [Int.cast_div_charZero (sign_target_dvd c d hc)]
  push_cast
  rfl

theorem integer_normalization :
    ∀ (c d : ℕ), 1 < c → Nat.Coprime c 6 → 0 < d → Nat.Coprime c d →
      zExponent c d = 0 ∧ qExponent c d = 0 ∧ Even (signExponent c d) := by
  intro c d hc1 hc6 hd hcop
  have hcasts := integer_casts c d hc6
  have hrats := rational_exponents c d hc1 hd hcop
  have hz : ((zExponent c d : ℤ) : ℚ) = 0 := by
    rw [zExponent]
    push_cast
    rw [hcasts.1, hcasts.2.1]
    exact hrats.1
  have hq : ((qExponent c d : ℤ) : ℚ) = 0 := by
    rw [qExponent]
    push_cast
    rw [hcasts.1, hcasts.2.2.1, hcasts.2.2.2.1, hcasts.2.2.2.2]
    convert hrats.2.1 using 1 <;> ring
  have hz0 : zExponent c d = 0 := by exact_mod_cast hz
  have hq0 : qExponent c d = 0 := by exact_mod_cast hq
  have hsign : ((signExponent c d : ℤ) : ℚ) =
      ((c : ℚ) - 1) * ((d : ℚ) - 1) *
        (1 - (c : ℚ) * ((d : ℚ) + 1)) / 2 := by
    rw [signExponent]
    push_cast
    rw [hcasts.1, hcasts.2.1]
    exact hrats.2.2
  have hsign_eq : signExponent c d =
      (((c : ℤ) - 1) * ((d : ℤ) - 1) *
        (1 - (c : ℤ) * ((d : ℤ) + 1))) / 2 := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
    rw [cast_sign_target c d hc6]
    exact hsign
  refine ⟨hz0, hq0, ?_⟩
  rw [hsign_eq]
  have hodd : Odd (c : ℤ) := by
    have hcop2 : Nat.Coprime c 2 := Nat.Coprime.of_dvd_right (by norm_num) hc6
    exact_mod_cast (Nat.coprime_two_right.mp hcop2)
  exact ArithmeticThetaElementary.norm_sign_exponent_even (c : ℤ) (d : ℤ) hodd

end ArithmeticThetaNormFiniteR0063
