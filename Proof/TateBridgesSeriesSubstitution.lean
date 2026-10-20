module

public import TateSeriesStabilization

@[expose] public section

/-! Ramified substitution for the literal normalized Tate annular series. -/
noncomputable section
universe u
namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

private theorem expand_formal_inv {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (f : PowerSeries k) :
    PowerSeries.expand m hm f⁻¹ = (PowerSeries.expand m hm f)⁻¹ := by
  by_cases hf : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr hf, map_zero,
      PowerSeries.inv_eq_zero.mpr (by simpa using hf)]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa using hf)).2
    rw [← map_mul, PowerSeries.inv_mul_cancel f hf, map_one]

private theorem expand_annular_monomial {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (a : k) (n : ℕ) :
    PowerSeries.expand m hm (monomial a n) = monomial a (m*n) := by
  simp [monomial, map_mul, map_pow, PowerSeries.expand_C, pow_mul]

private theorem expand_xTerm {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (f : PowerSeries k) :
    PowerSeries.expand m hm (xTerm f) = xTerm (PowerSeries.expand m hm f) := by
  simp only [xTerm, map_mul, map_pow, expand_formal_inv, map_sub, map_one]

private theorem expand_yTerm {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (f : PowerSeries k) :
    PowerSeries.expand m hm (yTerm f) = yTerm (PowerSeries.expand m hm f) := by
  simp only [yTerm, map_mul, map_pow, expand_formal_inv, map_sub, map_add, map_one]

/-- Expansion respects each finite normalized X sum, including its correction. -/
theorem expand_partialX {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (d i : ℕ) (a : k) (N : ℕ) :
    PowerSeries.expand m hm (partialX d i a N) = partialX (m*d) (m*i) a N := by
  simp only [partialX, map_sub, map_add, map_mul, map_sum, map_ofNat,
    expand_xTerm, expand_annular_monomial, PowerSeries.expand_C,
    expand_formal_inv, map_one, Nat.mul_add, Nat.mul_sub_left_distrib, Nat.mul_assoc]

/-- Expansion respects each finite Y sum and its one-half normalization. -/
theorem expand_partialY {k : Type u} [Field k]
    (m : ℕ) (hm : m ≠ 0) (d i : ℕ) (a : k) (N : ℕ) :
    PowerSeries.expand m hm (partialY d i a N) = partialY (m*d) (m*i) a N := by
  simp only [partialY, map_mul, map_add, map_sub, map_sum, PowerSeries.expand_C,
    expand_yTerm, expand_annular_monomial,
    Nat.mul_add, Nat.mul_sub_left_distrib, Nat.mul_assoc]

/-- Literal ramification t ↦ t^m commutes with both stabilized annular series. -/
theorem ramified_substitution {k : Type u} [Field k] [CharZero k]
    (m d i : ℕ) (a : k) (hm : 0 < m) (ha : Admissible d i a) :
    tateX (m*d) (m*i) a = PowerSeries.expand m (Nat.ne_of_gt hm) (tateX d i a) ∧
    tateY (m*d) (m*i) a = PowerSeries.expand m (Nat.ne_of_gt hm) (tateY d i a) := by
  constructor
  · ext n
    simp only [tateX, PowerSeries.coeff_mk]
    rw [← expand_partialX m hm.ne', PowerSeries.coeff_expand,
      PowerSeries.coeff_expand]
    split_ifs with h
    · simpa only [PowerSeries.coeff_mk] using
        (annular_stabilization d i a ha (n / m) (n+1)
          (Nat.add_le_add_right (Nat.div_le_self n m) 1)).1
    · rfl
  · ext n
    simp only [tateY, PowerSeries.coeff_mk]
    rw [← expand_partialY m hm.ne', PowerSeries.coeff_expand,
      PowerSeries.coeff_expand]
    split_ifs with h
    · simpa only [PowerSeries.coeff_mk] using
        (annular_stabilization d i a ha (n / m) (n+1)
          (Nat.add_le_add_right (Nat.div_le_self n m) 1)).2
    · rfl

end ArithmeticThetaTateBridges
