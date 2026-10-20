module

public import ScaledThetaExponentControlR0050

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050

open ArithmeticThetaScaledTateBridgeR0046
open ArithmeticThetaScaledTateCompletionExtensionR0048

variable (k : Type u) [Field k] [CharZero k]

theorem specialization_node_agreement (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0) (z : Node k r) :
    specialization k r i hr hi a ha (toCompleted k r z) =
      nodeMap k r i hr hi a ha z := by
  exact DFunLike.congr_fun
    (Classical.choose_spec
      (completion_specialization_exists_and_filtered k r i hr hi a ha)).1 z

theorem specialization_base (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0) (f : PowerSeries k) :
    specialization k r i hr hi a ha (completedBaseMap k r f) = f := by
  change specialization k r i hr hi a ha
    (toCompleted k r (algebraMap (Base k) (Node k r) f)) = f
  rw [specialization_node_agreement]
  change nodeMap k r i hr hi a ha
    (quotientMap k r (MvPolynomial.C f)) = f
  simp [nodeMap, quotientMap, baseMap]

theorem specialization_coordinates (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0) :
    specialization k r i hr hi a ha (tau k r) = PowerSeries.X ∧
    specialization k r i hr hi a ha (cx k r) =
      PowerSeries.C a * PowerSeries.X ^ i ∧
    specialization k r i hr hi a ha (cy k r) =
      PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i) := by
  refine ⟨specialization_base k r i hr hi a ha _, ?_, ?_⟩
  · rw [cx, specialization_node_agreement]
    exact (node_map_coordinates k r i hr hi a ha).2.1
  · rw [cy, specialization_node_agreement]
    exact (node_map_coordinates k r i hr hi a ha).2.2

theorem specialized_exponent_nat_pos (r i d j n : ℕ) (hr : 0 < r) (hd : 0 < d) :
    (specializedExponent r i d j (n : ℤ)).toNat =
      (thetaExponent r d j (n : ℤ)).toNat + i * n := by
  have hE := (theta_exponent_control r d j hr hd).1 (n : ℤ)
  have heq : specializedExponent r i d j (n : ℤ) =
      thetaExponent r d j (n : ℤ) + (i * n : ℕ) := by
    simp [specializedExponent, thetaExponent]
    ring
  rw [heq, Int.toNat_add hE (by positivity), Int.toNat_natCast]

theorem specialized_exponent_nat_neg (r i d j n : ℕ) (hr : 0 < r)
    (hi : i < r) (hd : 0 < d) :
    (specializedExponent r i d j (-(n + 1 : ℕ) : ℤ)).toNat =
      (thetaExponent r d j (-(n + 1 : ℕ) : ℤ)).toNat + (r - i) * (n + 1) := by
  have hE := (theta_exponent_control r d j hr hd).1 (-(n + 1 : ℕ) : ℤ)
  have heq : specializedExponent r i d j (-(n + 1 : ℕ) : ℤ) =
      thetaExponent r d j (-(n + 1 : ℕ) : ℤ) + ((r - i) * (n + 1) : ℕ) := by
    have hn : ¬ (0 : ℤ) ≤ -(n + 1 : ℕ) := by omega
    unfold specializedExponent thetaExponent
    rw [if_neg hn]
    push_cast [Nat.cast_sub (Nat.le_of_lt hi)]
    ring
  rw [heq, Int.toNat_add hE (by positivity), Int.toNat_natCast]

theorem theta_term_specialization (r i d j : ℕ) (hr : 0 < r)
    (hi : i < r) (hd : 0 < d) (a : k) (ha : a ≠ 0) (b : ℤ) :
    specialization k r i hr hi a ha (thetaTerm k r d j b) =
      specializedTerm k r i d j a b := by
  obtain ⟨ht, hx, hy⟩ := specialization_coordinates k r i hr hi a ha
  cases b with
  | ofNat n =>
    simp only [thetaTerm, Int.ofNat_eq_natCast, Int.natCast_nonneg, if_pos,
      Int.toNat_natCast, map_mul, map_pow, ht, hx, specializedTerm,
      zpow_natCast, specialized_exponent_nat_pos r i d j n hr hd,
      pow_add, mul_pow]
    rw [← map_pow, ← pow_mul]
    ring
  | negSucc n =>
    have hb : (Int.negSucc n : ℤ) = -(n + 1 : ℕ) := rfl
    rw [hb]
    have hn : ¬ (0 : ℤ) ≤ -(n + 1 : ℕ) := by omega
    simp only [thetaTerm, if_neg hn, neg_neg, Int.toNat_natCast,
      map_mul, map_pow, ht, hy, specializedTerm,
      specialized_exponent_nat_neg r i d j n hr hi hd,
      zpow_neg, zpow_natCast]
    rw [← inv_pow, map_pow]
    simp only [mul_pow, ← pow_mul, pow_add]
    ring

theorem theta_finite_specialization :
    ∀ (k : Type u) [Field k] [CharZero k] (r i m d j : ℕ) (nu : ℤ)
      (hr : 0 < r) (hi : i < r) (hd : 0 < d) (a : k) (ha : a ≠ 0) (N : ℕ),
      specialization k r i hr hi a ha (thetaPartial k r m d j nu N) =
        specializedPartial k r i m d j nu a N := by
  intro k _ _ r i m d j nu hr hi hd a ha N
  classical
  unfold thetaPartial specializedPartial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs with hres
  · exact theta_term_specialization k r i d j hr hi hd a ha b
  · exact map_zero _

end ArithmeticThetaScaledAnnularR0050
