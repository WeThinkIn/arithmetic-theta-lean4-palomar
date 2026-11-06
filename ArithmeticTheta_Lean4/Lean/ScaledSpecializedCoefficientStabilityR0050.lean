import ScaledAnnularDefinitionsR0050

set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaScaledAnnularR0050

open scoped BigOperators

private lemma exp_nonneg (r i d j : ℕ) (hr : 0 < r) (hi : i < r) (hd : 0 < d)
    (b : ℤ) : 0 ≤ specializedExponent r i d j b := by
  unfold specializedExponent thetaShift
  push_cast
  by_cases hb : 0 ≤ b
  · have hj : (0 : ℤ) ≤ j := by omega
    have hd' : (0 : ℤ) < d := by omega
    positivity
  · have hb' : b ≤ -1 := by omega
    have hs : (0 : ℤ) ≤ j + r := by omega
    have hji : (j + i : ℕ) ≤ j + r - 1 := by omega
    have hji' : (j + i : ℤ) ≤ (j + r : ℤ) - 1 := by omega
    have hsq : 0 ≤ ((-b : ℤ) - (j + r : ℤ)) ^ 2 := sq_nonneg _
    have hc : 0 ≤ -b := by omega
    have hcpos : 0 < -b := by omega
    have hd' : (1 : ℤ) ≤ d := by omega
    have hquad : 0 ≤ (-b : ℤ) ^ 2 - (j + r : ℤ) * (-b : ℤ) +
        (j + r : ℤ) ^ 2 := by nlinarith
    have hp := mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (sq_nonneg b)
    have hl := mul_nonneg (show (0 : ℤ) ≤ (j + r : ℤ) - (j + i : ℤ) by omega) hc
    nlinarith

private lemma exp_gt_of_abs_ge (r i d j n : ℕ) (hr : 0 < r) (hi : i < r)
    (hd : 0 < d) {b : ℤ} (hpos : (n + 2 * (j + r) + 1 : ℕ) ≤ b.natAbs) :
    (n : ℤ) < specializedExponent r i d j b := by
  unfold specializedExponent thetaShift
  push_cast
  have hs : (0 : ℤ) ≤ j + r := by omega
  have hji : (j + i : ℤ) ≤ (j + r : ℤ) - 1 := by omega
  have hd' : (1 : ℤ) ≤ d := by omega
  have hp := mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (sq_nonneg b)
  by_cases hb : 0 ≤ b
  · have habs : (b.natAbs : ℤ) = b := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb]
    have hbn : (n : ℤ) + 2 * (j + r : ℤ) + 1 ≤ b := by omega
    have hj : 0 ≤ ((j : ℤ) + i) * b := mul_nonneg (by omega) hb
    have hsq := mul_nonneg (show (0 : ℤ) ≤ b - 1 by omega) hb
    nlinarith [sq_nonneg (j + r : ℤ)]
  · have habs : (b.natAbs : ℤ) = -b := by
      rw [Int.natCast_natAbs, abs_of_neg (by omega)]
    have hbn : (n : ℤ) + 2 * (j + r : ℤ) + 1 ≤ -b := by omega
    have hc : 0 ≤ -b := by omega
    have hl := mul_nonneg (show (0 : ℤ) ≤ (j + r : ℤ) - (j + i : ℤ) by omega) hc
    have hprod := mul_nonneg (show (0 : ℤ) ≤ -b - (j + r : ℤ) - 1 by omega)
      (show (0 : ℤ) ≤ -b by omega)
    nlinarith [sq_nonneg (j + r : ℤ)]

private lemma coeff_specializedTerm (k : Type u) [Field k] (r i d j : ℕ) (a : k)
    (b : ℤ) (n : ℕ) :
    PowerSeries.coeff n (specializedTerm k r i d j a b) =
      if n = (specializedExponent r i d j b).toNat then a ^ b else 0 := by
  unfold specializedTerm
  rw [PowerSeries.coeff_C_mul_X_pow]

private lemma coeff_term_zero_of_lt (k : Type u) [Field k] (r i d j : ℕ) (a : k)
    (b : ℤ) (n : ℕ) (h : (n : ℤ) < specializedExponent r i d j b) :
    PowerSeries.coeff n (specializedTerm k r i d j a b) = 0 := by
  rw [coeff_specializedTerm]
  have hn : n ≠ (specializedExponent r i d j b).toNat := by
    intro he
    have hnon : 0 ≤ specializedExponent r i d j b := by omega
    have he' := congrArg (fun z : ℕ => (z : ℤ)) he
    rw [Int.toNat_of_nonneg hnon] at he'
    omega
  simp [hn]

 theorem specialized_coefficient_stability :
    ∀ (k : Type u) [Field k] [CharZero k] (r i m d j : ℕ) (nu : ℤ) (a : k),
      0 < r → i < r → 0 < m → Even m → 0 < d → a ≠ 0 →
      (∀ b : ℤ, 0 ≤ specializedExponent r i d j b) ∧
      (∀ (n N : ℕ), n + 2 * (j + r) + 1 ≤ N →
        PowerSeries.coeff n (specializedPartial k r i m d j nu a N) =
          PowerSeries.coeff n (specializedSeries k r i m d j nu a)) := by
  intro k _ _ r i m d j nu a hr hi hm hme hd ha
  constructor
  · intro b
    exact exp_nonneg r i d j hr hi hd b
  · intro n N hN
    rw [specializedSeries, PowerSeries.coeff_mk]
    unfold specializedPartial
    simp only [map_sum]
    symm
    apply Finset.sum_subset
    · apply Finset.Icc_subset_Icc <;> omega
    · intro b hb hbn
      simp only [Finset.mem_Icc] at hb hbn
      have habs : (n + 2 * (j + r) + 1 : ℕ) ≤ b.natAbs := by
        have habs' : -(b.natAbs : ℤ) ≤ b ∧ b ≤ b.natAbs := by
          rw [Int.natCast_natAbs]
          exact ⟨neg_abs_le b, le_abs_self b⟩
        omega
      have hegt := exp_gt_of_abs_ge r i d j n hr hi hd habs
      split <;> rename_i hres
      · exact coeff_term_zero_of_lt k r i d j a b n hegt
      · simp

end ArithmeticThetaScaledAnnularR0050
