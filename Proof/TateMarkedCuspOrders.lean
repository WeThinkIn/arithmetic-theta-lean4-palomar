module

public import TateSeriesCuspTerms

@[expose] public section

/-! Lower-coefficient vanishing for the literal marked Tate series.
The leading-coefficient theorem is imported unchanged from TateSeriesCuspTerms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaTateIdentities
open ArithmeticThetaTateSeries
variable {k : Type u} [Field k]

private lemma monomial_mul_coeff_zero (a : k) {r n : ℕ}
    (h : n < r) (g : PowerSeries k) :
    PowerSeries.coeff n (monomial a r * g) = 0 := by
  rw [monomial, mul_assoc, PowerSeries.coeff_C_mul]
  simp [PowerSeries.coeff_X_pow_mul', Nat.not_le_of_lt h]

private lemma x_coeff_zero (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (xTerm (monomial a r)) = 0 :=
  monomial_mul_coeff_zero a h _

private lemma y_coeff_zero (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (yTerm (monomial a r)) = 0 := by
  rw [yTerm, mul_assoc]
  exact monomial_mul_coeff_zero a h _

/-- In the first half of the annulus, both coordinates vanish below i. -/
lemma annular_vanishing (d i : ℕ) (a : k) (hi : 2 * i ≤ d) :
    AgreeBelow i (tateX d i a) 0 ∧ AgreeBelow i (tateY d i a) 0 := by
  have bounds (n j : ℕ) (hn : n < i) :
      n < d * (j + 1) + i ∧ n < d * (j + 1) - i ∧ n < d * (j + 1) := by
    have hd : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
    omega
  constructor
  · intro n hn
    have hs : PowerSeries.coeff n
        (∑ j ∈ Finset.range (n+1),
          (xTerm (monomial a (d*(j+1)+i)) +
          xTerm (monomial a⁻¹ (d*(j+1)-i)))) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_add, x_coeff_zero a (bounds n j hn).1,
        x_coeff_zero a⁻¹ (bounds n j hn).2.1, add_zero]
    have hc : PowerSeries.coeff n
        (∑ j ∈ Finset.range (n+1),
          PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
            (1 - monomial 1 (d*(j+1)))⁻¹) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [mul_assoc, PowerSeries.coeff_C_mul,
        monomial_mul_coeff_zero (1:k) (bounds n j hn).2.2, mul_zero]
    simp only [tateX, PowerSeries.coeff_mk, partialX, two_mul, map_sub, map_add]
    rw [x_coeff_zero a hn, hs, hc]
    simp
  · intro n hn
    have hs : PowerSeries.coeff n
        (∑ j ∈ Finset.range (n+1),
          (yTerm (monomial a (d*(j+1)+i)) -
          yTerm (monomial a⁻¹ (d*(j+1)-i)))) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_sub, y_coeff_zero a (bounds n j hn).1,
        y_coeff_zero a⁻¹ (bounds n j hn).2.1, sub_zero]
    simp only [tateY, PowerSeries.coeff_mk, partialY, PowerSeries.coeff_C_mul, map_add]
    rw [y_coeff_zero a hn, hs]
    simp

/-- Exact frozen marked-cusp vanishing obligation, with positive Tate period. -/
theorem marked_cusp_vanishing :
    ∀ {k : Type u} [Field k] [CharZero k], ∀ (m : ℕ), 0 < m →
      AgreeBelow (2*m) (tateX (4*m) (2*m) (1 : k)) 0 ∧
      AgreeBelow (2*m) (tateX (4*m) (2*m) (-1 : k)) 0 ∧
      AgreeBelow m (tateX (4*m) m (1 : k)) 0 ∧
      AgreeBelow m (tateY (4*m) m (1 : k)) 0 := by
  intro k _ _ m _hm
  exact ⟨(annular_vanishing (4*m) (2*m) (1:k) (by omega)).1,
    (annular_vanishing (4*m) (2*m) (-1:k) (by omega)).1,
    annular_vanishing (4*m) m (1:k) (by omega)⟩

end ArithmeticThetaTateIdentities
