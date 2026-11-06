import Mathlib

/-! Integrality of the `t`-power in the local numerator at `r = 2c`. -/
set_option autoImplicit false

namespace ArithmeticThetaLocalNormR0054

private theorem six_dvd_c_mul_square_sub_one (c : ℕ) (hc : 1 < c) :
    6 ∣ c * (c ^ 2 - 1) := by
  have h : (3 : ℕ).factorial ∣ (c + 1).descFactorial 3 :=
    Nat.factorial_dvd_descFactorial (c + 1) 3
  norm_num [Nat.descFactorial] at h
  have hc1 : 1 ≤ c := by omega
  have hone : 1 ≤ c ^ 2 := by nlinarith
  have hsub : c + 1 - 2 = c - 1 := by omega
  rw [hsub] at h
  have hpoly : c ^ 2 - 1 = (c - 1) * (c + 1) := by
    apply Nat.cast_injective (R := Int)
    push_cast [Nat.cast_sub hone, Nat.cast_sub hc1]
    ring
  simpa [hpoly, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem norm_exponent_integral (c : ℕ) (hc : 1 < c) (_hcop : Nat.Coprime c 6) :
    12 ∣ 2 * c * (c ^ 2 - 1) ∧
      ((2 * c * (c ^ 2 - 1) / 12 : ℕ) : ℚ) =
        (2 * c : ℚ) * ((c : ℚ) ^ 2 - 1) / 12 := by
  have h6 : 6 ∣ c * (c ^ 2 - 1) := six_dvd_c_mul_square_sub_one c hc
  have h12 : 12 ∣ 2 * c * (c ^ 2 - 1) := by
    have h' : 2 * 6 ∣ 2 * (c * (c ^ 2 - 1)) := Nat.mul_dvd_mul_left 2 h6
    norm_num at h' ⊢
    simpa [Nat.mul_assoc] using h'
  constructor
  · exact h12
  · rw [Nat.cast_div h12 (by norm_num)]
    have hone : 1 ≤ c ^ 2 := by nlinarith
    push_cast [Nat.cast_sub hone]
    ring

end ArithmeticThetaLocalNormR0054
