module

public import TateSeriesStabilization
public import TateLegacySeriesStabilization
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ENatToNat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k]
lemma expand_inv_one_sub (m : ℕ) (hm : m ≠ 0) (v : PowerSeries k)
    (hv : PowerSeries.constantCoeff v ≠ 1) :
    PowerSeries.expand m hm ((1-v)⁻¹) = (1 - PowerSeries.expand m hm v)⁻¹ := by
  have hψ : PowerSeries.constantCoeff (1 - PowerSeries.expand m hm v) ≠ 0 := by
    rw [map_sub (PowerSeries.constantCoeff), PowerSeries.constantCoeff_one]
    rw [PowerSeries.constantCoeff_expand]
    intro hzero
    exact (hv ((sub_eq_zero.mp hzero).symm)).elim
  apply (PowerSeries.eq_inv_iff_mul_eq_one hψ).2
  have hsub : (1 - PowerSeries.expand m hm v) = PowerSeries.expand m hm (1-v) := by
    rw [map_sub, map_one]
  rw [hsub, ← map_mul]
  rw [PowerSeries.inv_mul_cancel (1-v) (by
    rw [map_sub (PowerSeries.constantCoeff), PowerSeries.constantCoeff_one]
    exact sub_ne_zero.mpr (Ne.symm hv)), map_one]

lemma expand_monomial (m : ℕ) (hm : m ≠ 0) (a : k) (r : ℕ) :
    PowerSeries.expand m hm (monomial a r) = monomial a (m*r) := by
  unfold monomial
  rw [map_mul]
  rw [PowerSeries.expand_apply, PowerSeries.subst_C, PowerSeries.expand_apply]
  change PowerSeries.C a * (PowerSeries.subst (R := k) (S := k) (τ := Unit) (PowerSeries.X ^ m) (PowerSeries.X ^ r) : PowerSeries k) = _
  have ha : PowerSeries.HasSubst (PowerSeries.X ^ m : PowerSeries k) := PowerSeries.HasSubst.X_pow hm
  rw [PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
  rw [← pow_mul]

lemma expand_xTerm_monomial (m : ℕ) (hm : m ≠ 0) (a : k) (r : ℕ)
    (hr : PowerSeries.constantCoeff (monomial a r) ≠ 1) :
    PowerSeries.expand m hm (xTerm (monomial a r)) =
      xTerm (monomial a (m*r)) := by
  unfold xTerm
  rw [map_mul, map_pow, expand_inv_one_sub m hm _ hr, expand_monomial]

lemma expand_yTerm_monomial (m : ℕ) (hm : m ≠ 0) (a : k) (r : ℕ)
    (hr : PowerSeries.constantCoeff (monomial a r) ≠ 1) :
    PowerSeries.expand m hm (yTerm (monomial a r)) =
      yTerm (monomial a (m*r)) := by
  unfold yTerm
  rw [map_mul, map_mul, map_add, map_one, map_pow,
    expand_inv_one_sub m hm _ hr, expand_monomial]

lemma cc_monomial_ne_one_of_pos (a : k) {r : ℕ} (hr : 0 < r) :
    PowerSeries.constantCoeff (monomial a r) ≠ 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [monomial, PowerSeries.coeff_mul_X_pow', Nat.not_le_of_lt hr]

lemma cc_monomial_zero_ne_one (a : k) (ha : a ≠ 1) :
    PowerSeries.constantCoeff (monomial a 0) ≠ 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [monomial, PowerSeries.coeff_mul_X_pow', ha]

lemma expand_xTerm_base (m : ℕ) (hm : m ≠ 0) (d i : ℕ) (a : k)
    (hi : i = 0 → a ≠ 1) (hd : 0 < d) (hdi : i < d) :
    PowerSeries.expand m hm (xTerm (monomial a i)) =
      xTerm (monomial a (m*i)) := by
  apply expand_xTerm_monomial m hm
  by_cases hz : i = 0
  · simpa [hz] using cc_monomial_zero_ne_one a (hi hz)
  · exact cc_monomial_ne_one_of_pos a (Nat.pos_of_ne_zero hz)

lemma expand_yTerm_base (m : ℕ) (hm : m ≠ 0) (d i : ℕ) (a : k)
    (hi : i = 0 → a ≠ 1) (hd : 0 < d) (hdi : i < d) :
    PowerSeries.expand m hm (yTerm (monomial a i)) =
      yTerm (monomial a (m*i)) := by
  apply expand_yTerm_monomial m hm
  by_cases hz : i = 0
  · simpa [hz] using cc_monomial_zero_ne_one a (hi hz)
  · exact cc_monomial_ne_one_of_pos a (Nat.pos_of_ne_zero hz)

end ArithmeticThetaTateSeries
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k]
lemma expand_C (m : ℕ) (hm : m ≠ 0) (c : k) :
    PowerSeries.expand m hm (PowerSeries.C c) = PowerSeries.C c := by
  change PowerSeries.expand m hm ((algebraMap k (PowerSeries k)) c) = _
  rw [AlgHom.commutes]
  rfl

lemma expand_corr (m : ℕ) (hm : m ≠ 0) (c : k) (r : ℕ) (hr : 0 < r) :
    PowerSeries.expand m hm (PowerSeries.C c * monomial 1 r *
      (1 - monomial 1 r)⁻¹) =
      PowerSeries.C c * monomial 1 (m*r) *
        (1 - monomial 1 (m*r))⁻¹ := by
  rw [map_mul, map_mul, expand_C, expand_monomial,
    expand_inv_one_sub m hm _ (cc_monomial_ne_one_of_pos 1 hr), expand_monomial]

lemma expand_partialX (m d i : ℕ) (a : k) (N : ℕ)
    (hm : m ≠ 0) (hd : 0 < d) (hi : i < d)
    (ha : i = 0 → a ≠ 1) :
    PowerSeries.expand m hm (partialX d i a N) =
      partialX (m*d) (m*i) a N := by
  have htail : PowerSeries.expand m hm
      (∑ j ∈ Finset.range N,
        (xTerm (monomial a (d*(j+1)+i)) +
         xTerm (monomial a⁻¹ (d*(j+1)-i)))) =
      ∑ j ∈ Finset.range N,
        (xTerm (monomial a (m*d*(j+1)+m*i)) +
         xTerm (monomial a⁻¹ (m*d*(j+1)-m*i))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_add,
      expand_xTerm_monomial m hm a (d * (j + 1) + i)
        (cc_monomial_ne_one_of_pos a (by
          have h : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
          omega)),
      expand_xTerm_monomial m hm a⁻¹ (d * (j + 1) - i)
        (cc_monomial_ne_one_of_pos a⁻¹ (by
          have h : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
          omega))]
    congr 2 <;> simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hcorr : PowerSeries.expand m hm
      (∑ j ∈ Finset.range N,
        PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
          (1 - monomial 1 (d*(j+1)))⁻¹) =
      ∑ j ∈ Finset.range N,
        PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (m*d*(j+1)) *
          (1 - monomial 1 (m*d*(j+1)))⁻¹ := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [expand_corr m hm _ _ (by
      have h : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
      omega)]
    congr 2 <;> simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have htwo : PowerSeries.expand m hm (2 : PowerSeries k) = 2 := by
    change PowerSeries.expand m hm ((algebraMap k (PowerSeries k)) (2 : k)) = _
    rw [AlgHom.commutes]
    rfl
  unfold partialX
  rw [map_sub, map_add, expand_xTerm_base m hm d i a ha hd hi,
    htail, map_mul, hcorr, htwo]

lemma expand_partialY (m d i : ℕ) (a : k) (N : ℕ)
    (hm : m ≠ 0) (hd : 0 < d) (hi : i < d)
    (ha : i = 0 → a ≠ 1) :
    PowerSeries.expand m hm (partialY d i a N) =
      partialY (m*d) (m*i) a N := by
  have htail : PowerSeries.expand m hm
      (∑ j ∈ Finset.range N,
        (yTerm (monomial a (d*(j+1)+i)) -
         yTerm (monomial a⁻¹ (d*(j+1)-i)))) =
      ∑ j ∈ Finset.range N,
        (yTerm (monomial a (m*d*(j+1)+m*i)) -
         yTerm (monomial a⁻¹ (m*d*(j+1)-m*i))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_sub,
      expand_yTerm_monomial m hm a (d * (j + 1) + i)
        (cc_monomial_ne_one_of_pos a (by
          have h : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
          omega)),
      expand_yTerm_monomial m hm a⁻¹ (d * (j + 1) - i)
        (cc_monomial_ne_one_of_pos a⁻¹ (by
          have h : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right d (by omega)
          omega))]
    congr 2 <;> simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold partialY
  rw [map_mul, map_add, expand_yTerm_base m hm d i a ha hd hi, htail, expand_C]
end ArithmeticThetaTateSeries
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k] [CharZero k]

lemma tateX_coeff_div (m d i : ℕ) (a : k) (hm : m ≠ 0)
    (hd : 0 < d) (hi : i < d) (ha0 : a ≠ 0) (ha : i = 0 → a ≠ 1)
    {q : ℕ} :
    PowerSeries.coeff (m*q) (tateX (m*d) (m*i) a) =
      PowerSeries.coeff q (tateX d i a) := by
  simp only [tateX, PowerSeries.coeff_mk]
  change PowerSeries.coeff (m*q) (partialX (m*d) (m*i) a (m*q+1)) =
    PowerSeries.coeff q (partialX d i a (q+1))
  rw [← expand_partialX m d i a (m*q+1) hm hd hi ha]
  rw [PowerSeries.coeff_expand]
  simp only [if_pos (dvd_mul_right m q)]
  have hdiv : m*q / m = q := by
    rw [Nat.mul_comm, Nat.mul_div_left q (Nat.pos_of_ne_zero hm)]
  rw [hdiv]
  have hstab := annular_stabilization (k := k) d i a
    ⟨hd, hi, ha0, ha⟩ q (m*q+1) (by
      have hmq : q ≤ m*q := Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero hm)
      omega)
  rw [hstab.1]

lemma tateY_coeff_div (m d i : ℕ) (a : k) (hm : m ≠ 0)
    (hd : 0 < d) (hi : i < d) (ha0 : a ≠ 0) (ha : i = 0 → a ≠ 1)
    {q : ℕ} :
    PowerSeries.coeff (m*q) (tateY (m*d) (m*i) a) =
      PowerSeries.coeff q (tateY d i a) := by
  simp only [tateY, PowerSeries.coeff_mk]
  change PowerSeries.coeff (m*q) (partialY (m*d) (m*i) a (m*q+1)) =
    PowerSeries.coeff q (partialY d i a (q+1))
  rw [← expand_partialY m d i a (m*q+1) hm hd hi ha]
  rw [PowerSeries.coeff_expand]
  simp only [if_pos (dvd_mul_right m q)]
  have hdiv : m*q / m = q := by
    rw [Nat.mul_comm, Nat.mul_div_left q (Nat.pos_of_ne_zero hm)]
  rw [hdiv]
  have hstab := annular_stabilization (k := k) d i a
    ⟨hd, hi, ha0, ha⟩ q (m*q+1) (by
      have hmq : q ≤ m*q := Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero hm)
      omega)
  rw [hstab.2]

theorem ramified_substitution :
    ∀ {k : Type u} [Field k] [CharZero k] (m d i : ℕ) (a : k),
      (hm : 0 < m) → Admissible d i a →
        tateX (m*d) (m*i) a = PowerSeries.expand m (Nat.ne_of_gt hm) (tateX d i a) ∧
        tateY (m*d) (m*i) a = PowerSeries.expand m (Nat.ne_of_gt hm) (tateY d i a) := by
  intro k _ _ m d i a hm ⟨hd, hi, ha, haone⟩
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  constructor
  · apply PowerSeries.ext
    intro n
    by_cases hdiv : m ∣ n
    · obtain ⟨q, rfl⟩ := hdiv
      rw [tateX_coeff_div m d i a hm0 hd hi ha haone]
      rw [PowerSeries.coeff_expand]
      simp [hm0]
    · simp only [tateX, PowerSeries.coeff_mk]
      change PowerSeries.coeff n (partialX (m*d) (m*i) a (n+1)) = _
      rw [← expand_partialX m d i a (n+1) hm0 hd hi haone]
      simp only [PowerSeries.coeff_expand, hdiv, ↓reduceIte]
  · apply PowerSeries.ext
    intro n
    by_cases hdiv : m ∣ n
    · obtain ⟨q, rfl⟩ := hdiv
      rw [tateY_coeff_div m d i a hm0 hd hi ha haone]
      rw [PowerSeries.coeff_expand]
      simp [hm0]
    · simp only [tateY, PowerSeries.coeff_mk]
      change PowerSeries.coeff n (partialY (m*d) (m*i) a (n+1)) = _
      rw [← expand_partialY m d i a (n+1) hm0 hd hi haone]
      simp only [PowerSeries.coeff_expand, hdiv, ↓reduceIte]
end ArithmeticThetaTateSeries
