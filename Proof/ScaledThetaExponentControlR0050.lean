module

public import ScaledAnnularDefinitionsR0050
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaScaledAnnularR0050

theorem theta_exponent_control :
    ∀ (r d j : ℕ), 0 < r → 0 < d →
      (∀ b : ℤ, 0 ≤ thetaExponent r d j b) ∧
      (∀ (n : ℕ) (b : ℤ),
        (b < -((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) ∨
          ((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) < b) →
        (r * n : ℕ) ≤ (thetaExponent r d j b).toNat) := by
  intro r d j hr hd
  have hd1 : (1 : ℤ) ≤ (d : ℤ) := by omega
  have hs : (0 : ℤ) ≤ (j + r : ℕ) := by omega
  constructor
  · intro b
    unfold thetaExponent thetaShift
    by_cases hb : 0 ≤ b
    · simp [hb]
      have hdb : 0 ≤ (d : ℤ) * b ^ 2 :=
        mul_nonneg (by omega) (sq_nonneg b)
      have hjb : 0 ≤ (j : ℤ) * b :=
        mul_nonneg (by omega) hb
      nlinarith [sq_nonneg ((j + r : ℕ) : ℤ)]
    · simp [hb]
      have hquad : 0 ≤ b ^ 2 + ((j : ℤ) + (r : ℤ)) * b +
          ((j : ℤ) + (r : ℤ)) ^ 2 := by
        nlinarith [sq_nonneg (2 * b + (j : ℤ) + (r : ℤ)),
          sq_nonneg ((j : ℤ) + (r : ℤ))]
      nlinarith [sq_nonneg b]
  · intro n b hb
    unfold thetaExponent thetaShift
    by_cases hbp : 0 ≤ b
    · have hright : ((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) < b := by
        rcases hb with hleft | hright
        · omega
        · exact hright
      simp only [if_pos hbp]
      have hbrn : ((r * n : ℕ) : ℤ) ≤ b := by omega
      have hb1 : 0 ≤ b - 1 := by omega
      have hbprod : 0 ≤ b * (b - 1) := mul_nonneg hbp hb1
      have hb2 : ((r * n : ℕ) : ℤ) ≤ b ^ 2 := by
        nlinarith
      have hE : 0 ≤
          ((j + r : ℕ) : ℤ) ^ 2 + (d : ℤ) * b ^ 2 + (j : ℕ) * b := by
        nlinarith [sq_nonneg ((j + r : ℕ) : ℤ)]
      have hErn : ((r * n : ℕ) : ℤ) ≤
          ((j + r : ℕ) : ℤ) ^ 2 + (d : ℤ) * b ^ 2 + (j : ℕ) * b := by
        nlinarith [sq_nonneg ((j + r : ℕ) : ℤ)]
      have hnat := Int.toNat_le_toNat hErn
      simpa only [Int.toNat_natCast, Nat.cast_pow, Nat.cast_add] using hnat
    · have hleft : b < -((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) := by
        rcases hb with hleft | hright
        · exact hleft
        · omega
      have hc : ((r * n : ℕ) : ℤ) ≤ -b - (j + r : ℕ) := by
        omega
      have hcm : 0 ≤ -b - (j + r : ℕ) := by omega
      have hbm : 0 ≤ -b - 1 := by omega
      have hprod : ((r * n : ℕ) : ℤ) ≤
          (-b) * (-b - (j + r : ℕ)) := by
        nlinarith [mul_nonneg hbm hcm]
      simp only [if_neg hbp]
      have hE : 0 ≤
          ((j + r : ℕ) : ℤ) ^ 2 + (d : ℤ) * b ^ 2 + (j + r : ℕ) * b := by
        nlinarith [sq_nonneg b, hprod]
      have hErn : ((r * n : ℕ) : ℤ) ≤
          ((j + r : ℕ) : ℤ) ^ 2 + (d : ℤ) * b ^ 2 + (j + r : ℕ) * b := by
        nlinarith [sq_nonneg b, hprod]
      have hnat := Int.toNat_le_toNat hErn
      simpa only [Int.toNat_natCast, Nat.cast_pow, Nat.cast_add] using hnat

end ArithmeticThetaScaledAnnularR0050
