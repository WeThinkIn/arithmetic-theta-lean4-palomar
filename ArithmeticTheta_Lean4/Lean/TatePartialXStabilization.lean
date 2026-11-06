import TateCoeffMonomial
import TateCoeffXTerm

namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries

private theorem x_coeff_below {k : Type u} [Field k] (a : k) (m n : ℕ)
    (h : n < m) : PowerSeries.coeff n (xTerm (monomial a m)) = 0 := by
  rw [x_term_coeff a m n (by omega)]
  simp [Nat.div_eq_of_lt h]

private theorem correction_coeff_below {k : Type u} [Field k] (b : k) (m n : ℕ)
    (h : n < m) : PowerSeries.coeff n
      (PowerSeries.C b * monomial (1 : k) m * (1 - monomial 1 m)⁻¹) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpm : p.1 ≠ m := by omega
  rw [PowerSeries.coeff_C_mul, monomial_coeff]
  simp [hpm]

/-- Each coefficient of the literal normalized annular X sum stabilizes
    once the cutoff is at least one more than its degree. -/
theorem partial_x_stabilization {k : Type u} [Field k] (d i : ℕ) (a : k)
    (ha : ArithmeticThetaTateSeries.Admissible d i a) :
    ∀ n N : ℕ, n + 1 ≤ N →
      PowerSeries.coeff n (ArithmeticThetaTateSeries.partialX d i a N) =
        PowerSeries.coeff n (ArithmeticThetaTateSeries.partialX d i a (n+1)) := by
  intro n N hN
  have hd : 0 < d := ha.1
  have hi : i < d := ha.2.1
  have hbounds : ∀ j, n + 1 ≤ j →
      n < d * (j+1) + i ∧ n < d * (j+1) - i ∧ n < d * (j+1) := by
    intro j hj
    have hmul : j ≤ d * j := Nat.le_mul_of_pos_left j hd
    have hexp : d * (j+1) = d*j+d := by ring
    omega
  have hx : (∑ j ∈ Finset.range N, PowerSeries.coeff n
      (xTerm (monomial a (d*(j+1)+i)) +
       xTerm (monomial a⁻¹ (d*(j+1)-i)))) =
      ∑ j ∈ Finset.range (n+1), PowerSeries.coeff n
      (xTerm (monomial a (d*(j+1)+i)) +
       xTerm (monomial a⁻¹ (d*(j+1)-i))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro j _ hj
    have hb := hbounds j (by simpa using hj)
    rw [map_add, x_coeff_below a _ _ hb.1, x_coeff_below a⁻¹ _ _ hb.2.1]
    simp
  have hc : (∑ j ∈ Finset.range N, PowerSeries.coeff n
      (PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
       (1 - monomial 1 (d*(j+1)))⁻¹)) =
      ∑ j ∈ Finset.range (n+1), PowerSeries.coeff n
      (PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
       (1 - monomial 1 (d*(j+1)))⁻¹) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro j _ hj
    exact correction_coeff_below _ _ _ (hbounds j (by simpa using hj)).2.2
  simp only [partialX, two_mul, map_add, map_sub, map_sum]
  simp only [map_add] at hx
  rw [hx, hc]

end ArithmeticThetaTateBridges
