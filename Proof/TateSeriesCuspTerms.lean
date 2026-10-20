module

public import TateSeriesSubstitution

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
universe u
namespace ArithmeticThetaTateSeries

variable {k : Type u} [Field k] [CharZero k]

private lemma coeff_monomial_of_lt (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (monomial a r) = 0 := by
  simp [monomial, PowerSeries.coeff_mul_X_pow', Nat.not_le_of_lt h]

private lemma coeff_mul_of_left_zero (f g : PowerSeries k) (r n : ℕ)
    (hf : ∀ j < r, PowerSeries.coeff j f = 0) (h : n < r) :
    PowerSeries.coeff n (f * g) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hf x.1 (lt_of_le_of_lt
    (Finset.HasAntidiagonal.antidiagonal.fst_le hx) h), zero_mul]

private lemma coeff_xTerm_of_lt (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (xTerm (monomial a r)) = 0 := by
  exact coeff_mul_of_left_zero (monomial a r) (((1 - monomial a r)⁻¹)^2) r n
    (fun j hj => coeff_monomial_of_lt a hj) h

private lemma coeff_yTerm_of_lt (a : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (yTerm (monomial a r)) = 0 := by
  refine coeff_mul_of_left_zero (monomial a r * (1 + monomial a r))
    (((1 - monomial a r)⁻¹)^3) r n ?_ h
  intro j hj
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [coeff_monomial_of_lt a (lt_of_le_of_lt
    (Finset.HasAntidiagonal.antidiagonal.fst_le hx) hj), zero_mul]

private lemma coeff_corr_of_lt (c : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (PowerSeries.C c * monomial 1 r *
      (1 - monomial 1 r)⁻¹) = 0 := by
  exact coeff_mul_of_left_zero (PowerSeries.C c * monomial 1 r)
    ((1 - monomial 1 r)⁻¹) r n
    (fun j hj => by
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      rw [coeff_monomial_of_lt (1 : k) (lt_of_le_of_lt
        (Finset.HasAntidiagonal.antidiagonal.snd_le hx) hj), mul_zero]) h

private lemma coeff_monomial_mul (a : k) (r : ℕ) (g : PowerSeries k) :
    PowerSeries.coeff r (monomial a r * g) = a * PowerSeries.coeff 0 g := by
  unfold monomial
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  congr 1
  simpa using (PowerSeries.coeff_X_pow_mul g r 0)

private lemma coeff_zero_inv_pow_of_pos (a : k) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    PowerSeries.coeff 0 ((1 - monomial a r)⁻¹ ^ q) = 1 := by
  have h := congrFun PowerSeries.coeff_zero_eq_constantCoeff
    ((1 - monomial a r)⁻¹ ^ q)
  rw [h]
  have hz : (0 : k) ^ r = 0 := zero_pow (Nat.ne_of_gt hr)
  simp [PowerSeries.constantCoeff_inv, monomial, hz]

private lemma coeff_xTerm_at (a : k) {r : ℕ} (hr : 0 < r) :
    PowerSeries.coeff r (xTerm (monomial a r)) = a := by
  rw [xTerm, coeff_monomial_mul, coeff_zero_inv_pow_of_pos a hr 2]
  simp

private lemma coeff_yTerm_at (a : k) {r : ℕ} (hr : 0 < r) :
    PowerSeries.coeff r (yTerm (monomial a r)) = a := by
  rw [yTerm, mul_assoc, coeff_monomial_mul]
  have h := congrFun PowerSeries.coeff_zero_eq_constantCoeff
    ((1 + monomial a r) * (1 - monomial a r)⁻¹ ^ 3)
  rw [h]
  have hz : (0 : k) ^ r = 0 := zero_pow (Nat.ne_of_gt hr)
  simp [PowerSeries.constantCoeff_inv, monomial, hz]

private lemma coeff_corr_simple_of_lt {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (monomial (1:k) r * (1 - monomial (1:k) r)⁻¹) = 0 := by
  exact coeff_mul_of_left_zero (monomial (1:k) r) ((1 - monomial (1:k) r)⁻¹) r n
    (fun j hj => coeff_monomial_of_lt (1 : k) hj) h

private lemma coeff_corr_right_of_lt (c : k) {r n : ℕ} (h : n < r) :
    PowerSeries.coeff n (PowerSeries.C c * (monomial (1:k) r *
      (1 - monomial (1:k) r)⁻¹)) = 0 := by
  rw [← mul_assoc]
  exact coeff_corr_of_lt c h

private lemma coeff_sum_tail (F : ℕ → PowerSeries k) {n : ℕ}
    (hz : ∀ j, 0 < j → PowerSeries.coeff n (F j) = 0) :
    PowerSeries.coeff n (∑ j ∈ Finset.range (n+1), F j) =
      PowerSeries.coeff n (F 0) := by
  rw [map_sum]
  apply Finset.sum_eq_single 0
  · intro j hj hj0
    exact hz j (Nat.pos_of_ne_zero (by simpa using hj0))
  · simp

theorem marked_cusp_terms :
    ∀ {k : Type u} [Field k] [CharZero k] (m : ℕ), 0 < m →
      PowerSeries.coeff 0 (tateX (4*m) 0 (-1 : k)) = -(4:k)⁻¹ ∧
      PowerSeries.coeff (2*m) (tateX (4*m) (2*m) (1:k)) = 2 ∧
      PowerSeries.coeff (2*m) (tateX (4*m) (2*m) (-1:k)) = -2 ∧
      PowerSeries.coeff m (tateX (4*m) m (1:k)) = 1 ∧
      PowerSeries.coeff m (tateY (4*m) m (1:k)) = (2:k)⁻¹ ∧
      PowerSeries.coeff (2*m)
        (tateX (4*m) (2*m) (1:k) - tateX (4*m) (2*m) (-1:k)) = 4 := by
  intro k _ _ m hm
  have b0 : PowerSeries.coeff 0 (tateX 4 0 (-1:k)) = -(4:k)⁻¹ := by
    simp only [tateX, PowerSeries.coeff_mk]
    rw [partialX]
    simp only [map_add, map_sub, map_mul, two_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, add_zero, zero_add, sub_zero, Nat.mul_one, Nat.sub_zero]
    rw [coeff_xTerm_of_lt (-1:k) (r := 4) (n := 0) (by norm_num),
      coeff_xTerm_of_lt ((-1:k)⁻¹) (r := 4) (n := 0) (by norm_num)]
    have hc2 : PowerSeries.constantCoeff (2 : PowerSeries k) = 2 := by
      change PowerSeries.constantCoeff (PowerSeries.C (2:k)) = 2
      simp
    norm_num [xTerm, monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
      PowerSeries.constantCoeff_inv, PowerSeries.coeff_mul_X_pow', hc2]
    change (4 : k)⁻¹ = 1 / 4
    simp only [one_div]
  have bp : PowerSeries.coeff 2 (tateX 4 2 (1:k)) = 2 := by
    simp only [tateX, PowerSeries.coeff_mk]
    rw [partialX]
    simp only [map_add, map_sub, map_mul, two_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, add_zero, zero_add, sub_zero, inv_one, inv_neg]
    simp [coeff_xTerm_at (1:k) (r := 2) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 6) (n := 2) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 10) (n := 2) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 14) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (1:k)) (r := 4) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (2:k)) (r := 8) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (3:k)) (r := 12) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 4) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 8) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 12) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (1:k)) (r := 4) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (2:k)) (r := 8) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (3:k)) (r := 12) (n := 2) (by norm_num)]
    norm_num
  have bn : PowerSeries.coeff 2 (tateX 4 2 (-1:k)) = -2 := by
    simp only [tateX, PowerSeries.coeff_mk]
    rw [partialX]
    simp only [map_add, map_sub, map_mul, two_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, add_zero, zero_add, sub_zero, inv_one, inv_neg]
    simp [coeff_xTerm_at (-1:k) (r := 2) (by norm_num),
      coeff_xTerm_of_lt (-1:k) (r := 6) (n := 2) (by norm_num),
      coeff_xTerm_of_lt (-1:k) (r := 10) (n := 2) (by norm_num),
      coeff_xTerm_of_lt (-1:k) (r := 14) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (1:k)) (r := 4) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (2:k)) (r := 8) (n := 2) (by norm_num),
      coeff_corr_of_lt (c := (3:k)) (r := 12) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 4) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 8) (n := 2) (by norm_num),
      coeff_corr_simple_of_lt (r := 12) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (1:k)) (r := 4) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (2:k)) (r := 8) (n := 2) (by norm_num),
      coeff_corr_right_of_lt (c := (3:k)) (r := 12) (n := 2) (by norm_num)]
    norm_num
  have b1 : PowerSeries.coeff 1 (tateX 4 1 (1:k)) = 1 := by
    simp only [tateX, PowerSeries.coeff_mk]
    rw [partialX]
    simp only [map_add, map_sub, map_mul, two_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, add_zero, zero_add, sub_zero, inv_one, inv_neg]
    simp [coeff_xTerm_at (1:k) (r := 1) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 3) (n := 1) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 5) (n := 1) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 7) (n := 1) (by norm_num),
      coeff_xTerm_of_lt (1:k) (r := 9) (n := 1) (by norm_num),
      coeff_corr_of_lt (c := (1:k)) (r := 4) (n := 1) (by norm_num),
      coeff_corr_of_lt (c := (2:k)) (r := 8) (n := 1) (by norm_num),
      coeff_corr_simple_of_lt (r := 4) (n := 1) (by norm_num),
      coeff_corr_simple_of_lt (r := 8) (n := 1) (by norm_num),
      coeff_corr_right_of_lt (c := (1:k)) (r := 4) (n := 1) (by norm_num),
      coeff_corr_right_of_lt (c := (2:k)) (r := 8) (n := 1) (by norm_num)]
  have by1 : PowerSeries.coeff 1 (tateY 4 1 (1:k)) = (2:k)⁻¹ := by
    simp only [tateY, PowerSeries.coeff_mk]
    rw [partialY]
    rw [PowerSeries.coeff_C_mul]
    simp only [map_add, Finset.sum_range_succ, Finset.sum_range_zero,
      add_zero, zero_add, sub_zero]
    simp [coeff_yTerm_at (1:k) (r := 1) (by norm_num),
      coeff_yTerm_of_lt (1:k) (r := 3) (n := 1) (by norm_num),
      coeff_yTerm_of_lt (1:k) (r := 5) (n := 1) (by norm_num),
      coeff_yTerm_of_lt (1:k) (r := 7) (n := 1) (by norm_num),
      coeff_yTerm_of_lt (1:k) (r := 9) (n := 1) (by norm_num)]
  have h0 := ramified_substitution m 4 0 (-1:k) (by omega)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hp := ramified_substitution m 4 2 (1:k) (by omega)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hn := ramified_substitution m 4 2 (-1:k) (by omega)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have h1 := ramified_substitution m 4 1 (1:k) (by omega)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have c0 : PowerSeries.coeff 0 (tateX (m*4) (m*0) (-1:k)) = -(4:k)⁻¹ := by
    rw [h0.1, PowerSeries.coeff_expand]
    simp [Nat.ne_of_gt hm, b0]
  have cp : PowerSeries.coeff (m*2) (tateX (m*4) (m*2) (1:k)) = 2 := by
    rw [hp.1, PowerSeries.coeff_expand]
    simp [Nat.ne_of_gt hm, bp]
  have cn : PowerSeries.coeff (m*2) (tateX (m*4) (m*2) (-1:k)) = -2 := by
    rw [hn.1, PowerSeries.coeff_expand]
    simp [Nat.ne_of_gt hm, bn]
  have c1 : PowerSeries.coeff m (tateX (m*4) (m*1) (1:k)) = 1 := by
    rw [h1.1, PowerSeries.coeff_expand]
    have hmdiv : m / m = 1 := Nat.div_self hm
    simp [hmdiv, b1]
  have cy1 : PowerSeries.coeff m (tateY (m*4) (m*1) (1:k)) = (2:k)⁻¹ := by
    rw [h1.2, PowerSeries.coeff_expand]
    have hmdiv : m / m = 1 := Nat.div_self hm
    simp [hmdiv, by1]
  simp only [Nat.mul_comm, Nat.mul_zero, Nat.mul_one]
  refine ⟨c0, cp, cn, (by simpa using c1), (by simpa using cy1), ?_⟩
  rw [map_sub, cp, cn]
  norm_num

end ArithmeticThetaTateSeries
