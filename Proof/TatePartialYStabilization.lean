module

public import TateCoeffYTerm

@[expose] public section
open scoped BigOperators
namespace ArithmeticThetaTateBridges
open ArithmeticThetaTateSeries
open PowerSeries

variable {k : Type u} [Field k]

theorem partial_y_stabilization {k : Type u} [Field k] (d i : ℕ) (a : k)
    (hadm : ArithmeticThetaTateSeries.Admissible d i a) :
    ∀ n N : ℕ, n + 1 ≤ N →
      PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a N) =
        PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a (n+1)) := by
  intro n N hN
  rcases hadm with ⟨hd, hi, ha, ha1⟩
  -- The coefficient of every tail summand with index at least `n+1` is zero.
  have hzero : ∀ j : ℕ, n + 1 ≤ j →
      PowerSeries.coeff n
        (ArithmeticThetaTateSeries.yTerm (ArithmeticThetaTateSeries.monomial a (d*(j+1)+i)) -
         ArithmeticThetaTateSeries.yTerm (ArithmeticThetaTateSeries.monomial a⁻¹ (d*(j+1)-i))) = 0 := by
    intro j hj
    have hpos₁ : 0 < d * (j+1) + i := by
      have : 0 < d * (j+1) := Nat.mul_pos hd (Nat.succ_pos j)
      exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
    have hd1 : 1 ≤ d := hd
    have hdi : i + 1 ≤ d := hi
    have hmul₁ : (j+1) + i ≤ d * (j+1) := by
      have hmul := Nat.mul_le_mul_right (j+1) hdi
      have hadd : (j+1) + i ≤ (i+1) * (j+1) := by nlinarith
      exact le_trans hadd hmul
    have hmul₂ : j+1 ≤ d * (j+1) - i := Nat.le_sub_of_add_le hmul₁
    have hpos₂ : 0 < d * (j+1) - i := Nat.lt_of_lt_of_le (Nat.zero_lt_succ j) hmul₂
    have hmul₃ : j+1 ≤ d * (j+1) := by
      simpa using (Nat.mul_le_mul_right (j+1) hd1)
    have hdeg₁ : n < d * (j+1) + i := by omega
    have hdeg₂ : n < d * (j+1) - i := by
      exact lt_of_lt_of_le (by omega) hmul₂
    rw [map_sub,
      y_term_coeff a (d*(j+1)+i) n hpos₁,
      y_term_coeff a⁻¹ (d*(j+1)-i) n hpos₂]
    have hc₁ : (if d * (j+1) + i ∣ n then
        (((((n / (d*(j+1)+i) : ℕ)^2 : ℕ) : k) * a^(n/(d*(j+1)+i)))) else 0) = 0 := by
      by_cases hdiv : d * (j+1) + i ∣ n
      · have hn0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hdeg₁
        subst n
        simp
      · simp [hdiv]
    have hc₂ : (if d * (j+1) - i ∣ n then
        (((((n / (d*(j+1)-i) : ℕ)^2 : ℕ) : k) * (a⁻¹)^(n/(d*(j+1)-i)))) else 0) = 0 := by
      by_cases hdiv : d * (j+1) - i ∣ n
      · have hn0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hdeg₂
        subst n
        simp
      · simp [hdiv]
    rw [hc₁, hc₂]
    simp
  have hstep : ∀ M : ℕ, n + 1 ≤ M →
      PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a (M+1)) =
        PowerSeries.coeff n (ArithmeticThetaTateSeries.partialY d i a M) := by
    intro M hM
    rw [partialY, partialY]
    rw [Finset.sum_range_succ]
    simp only [map_mul, map_add, map_sub, coeff_C_mul]
    have hz := hzero M hM
    rw [map_sub] at hz
    rw [hz]
    ring
  -- Expand the finite sum one term at a time and discard the zero tail.
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
      exact (hstep N hN).trans ih

end ArithmeticThetaTateBridges
