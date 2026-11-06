import TateSeriesDefinitions

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaTateSeries

variable {k : Type u} [Field k]

private lemma coeff_monomial_of_lt (a : k) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (monomial a m) = 0 := by
  simp [monomial, PowerSeries.coeff_mul_X_pow', Nat.not_le_of_lt h]

private lemma coeff_mul_of_left_zero (f g : PowerSeries k) (m n : ℕ)
    (hf : ∀ i < m, PowerSeries.coeff i f = 0) (h : n < m) :
    PowerSeries.coeff n (f * g) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hf x.1 (lt_of_le_of_lt
    (Finset.HasAntidiagonal.antidiagonal.fst_le hx) h), zero_mul]

private lemma coeff_xTerm_of_lt (a : k) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (xTerm (monomial a m)) = 0 := by
  exact coeff_mul_of_left_zero (monomial a m) (((1 - monomial a m)⁻¹)^2) m n
    (fun i hi => coeff_monomial_of_lt a hi) h

private lemma coeff_yTerm_of_lt (a : k) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (yTerm (monomial a m)) = 0 := by
  refine coeff_mul_of_left_zero (monomial a m * (1 + monomial a m))
    (((1 - monomial a m)⁻¹)^3) m n ?_ h
  intro i hi
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [coeff_monomial_of_lt a (lt_of_le_of_lt
    (Finset.HasAntidiagonal.antidiagonal.fst_le hx) hi), zero_mul]

private lemma coeff_corr_of_lt (c : k) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (PowerSeries.C c * monomial 1 m *
      (1 - monomial 1 m)⁻¹) = 0 := by
  exact coeff_mul_of_left_zero (PowerSeries.C c * monomial 1 m)
    ((1 - monomial 1 m)⁻¹) m n
    (fun i hi => by
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      rw [coeff_monomial_of_lt (1 : k) (lt_of_le_of_lt
        (Finset.HasAntidiagonal.antidiagonal.snd_le hx) hi), mul_zero]
    ) h

private lemma coeff_sum_range_stable (F : ℕ → PowerSeries k) {n N : ℕ}
    (hN : n + 1 ≤ N) (hz : ∀ j, n + 1 ≤ j → PowerSeries.coeff n (F j) = 0) :
    PowerSeries.coeff n (∑ j ∈ Finset.range N, F j) =
      PowerSeries.coeff n (∑ j ∈ Finset.range (n + 1), F j) := by
  simp only [map_sum]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)
  · intro j hj hjnot
    apply hz j
    have hjN : j < N := Finset.mem_range.mp hj
    have hjsmall : ¬ j < n + 1 := by
      intro hjs
      exact hjnot (Finset.mem_range.mpr hjs)
    omega

private lemma coeff_positive_tail_zero (d i : ℕ) (hd : 0 < d) {n j : ℕ}
    (hj : n + 1 ≤ j) : n < d * (j + 1) + i := by
  have hmul : j + 1 ≤ d * (j + 1) := Nat.le_mul_of_pos_left (j + 1) hd
  omega

private lemma coeff_negative_tail_zero (d i : ℕ) (hd : 0 < d) (hi : i < d)
    {n j : ℕ} (hj : n + 1 ≤ j) : n < d * (j + 1) - i := by
  have hji : j ≤ d * j := Nat.le_mul_of_pos_left j hd
  have hid : i + 1 ≤ d := by omega
  have hadd : j + (i + 1) ≤ d * j + d := Nat.add_le_add hji hid
  have hdi : i ≤ d * (j + 1) := by
    have : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
    omega
  have hsub : j + 1 ≤ d * (j + 1) - i := by
    apply (Nat.le_sub_iff_add_le hdi).2
    rw [Nat.mul_add]
    omega
  omega

theorem annular_stabilization :
    ∀ {k : Type u} [Field k] [CharZero k] (d i : ℕ) (a : k),
      Admissible d i a → ∀ n N : ℕ, n + 1 ≤ N →
        PowerSeries.coeff n (partialX d i a N) =
          PowerSeries.coeff n (partialX d i a (n + 1)) ∧
        PowerSeries.coeff n (partialY d i a N) =
          PowerSeries.coeff n (partialY d i a (n + 1)) := by
  intro k _ _ d i a hadm n N hN
  rcases hadm with ⟨hd, hi, ha, haone⟩
  have hpos (j : ℕ) (hj : n + 1 ≤ j) :
      PowerSeries.coeff n
        (xTerm (monomial a (d * (j + 1) + i))) = 0 :=
    coeff_xTerm_of_lt a (coeff_positive_tail_zero d i hd hj)
  have hneg (j : ℕ) (hj : n + 1 ≤ j) :
      PowerSeries.coeff n
        (xTerm (monomial a⁻¹ (d * (j + 1) - i))) = 0 :=
    coeff_xTerm_of_lt a⁻¹ (coeff_negative_tail_zero d i hd hi hj)
  have hcorr (j : ℕ) (hj : n + 1 ≤ j) :
      PowerSeries.coeff n
        (PowerSeries.C ((j + 1 : ℕ) : k) * monomial 1 (d * (j + 1)) *
          (1 - monomial 1 (d * (j + 1)))⁻¹) = 0 :=
    coeff_corr_of_lt ((j + 1 : ℕ) : k)
      (by
        have hmul : j + 1 ≤ d * (j + 1) := Nat.le_mul_of_pos_left (j + 1) hd
        omega)
  have hsboth := coeff_sum_range_stable
    (fun j => xTerm (monomial a (d * (j + 1) + i)) +
      xTerm (monomial a⁻¹ (d * (j + 1) - i))) hN
    (fun j hj => by rw [map_add, hpos j hj, hneg j hj, add_zero])
  have hsdiff := coeff_sum_range_stable
    (fun j => yTerm (monomial a (d * (j + 1) + i)) -
      yTerm (monomial a⁻¹ (d * (j + 1) - i))) hN
    (fun j hj => by
      have hp : PowerSeries.coeff n
          (yTerm (monomial a (d * (j + 1) + i))) = 0 :=
        coeff_yTerm_of_lt a (coeff_positive_tail_zero d i hd hj)
      have hn : PowerSeries.coeff n
          (yTerm (monomial a⁻¹ (d * (j + 1) - i))) = 0 :=
        coeff_yTerm_of_lt a⁻¹ (coeff_negative_tail_zero d i hd hi hj)
      rw [map_sub, hp, hn, sub_zero])
  have hscorr := coeff_sum_range_stable
    (fun j => PowerSeries.C ((j + 1 : ℕ) : k) * monomial 1 (d * (j + 1)) *
      (1 - monomial 1 (d * (j + 1)))⁻¹) hN hcorr
  constructor
  · unfold partialX
    simp only [map_sub, map_add, two_mul]
    rw [hsboth, hscorr]
  · unfold partialY
    simp only [PowerSeries.coeff_C_mul, map_add]
    rw [hsdiff]

end ArithmeticThetaTateSeries
