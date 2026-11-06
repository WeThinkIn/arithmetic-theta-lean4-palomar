import TateSeriesDefinitions

namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

 theorem monomial_coeff {k : Type u} [Field k] (a : k) (m n : ℕ) :
    PowerSeries.coeff n (ArithmeticThetaTateSeries.monomial a m) = if n = m then a else 0 := by
  by_cases h : n = m
  · subst n
    simp [ArithmeticThetaTateSeries.monomial, PowerSeries.coeff_mul_X_pow']
  · by_cases hle : m ≤ n
    · have hlt : m < n := lt_of_le_of_ne hle (Ne.symm h)
      have hpos : 0 < n - m := Nat.sub_pos_of_lt hlt
      rw [ArithmeticThetaTateSeries.monomial, PowerSeries.coeff_mul_X_pow']
      simp [PowerSeries.coeff_C, hpos.ne']
      intro hn
      exact (h hn).elim
    · simp [ArithmeticThetaTateSeries.monomial, PowerSeries.coeff_mul_X_pow', h, hle]

end ArithmeticThetaTateBridges
