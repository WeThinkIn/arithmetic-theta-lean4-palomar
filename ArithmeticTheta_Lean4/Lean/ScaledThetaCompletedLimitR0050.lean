import ScaledThetaExponentControlR0050

/-! The scaled theta sum in the actual completed node, with its uniform cutoff. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050
open ArithmeticThetaScaledTateBridgeR0046

variable (k : Type u) [Field k]

lemma theta_completed_adic (r : ℕ) :
    IsAdicComplete (Ideal.span {completedParameter k r}) (CompletedNode k r) := by
  have hfg : (nodeIdeal k r).FG := Submodule.fg_span (by simp)
  have hmap : (nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r)) =
      Ideal.span {completedParameter k r} := by
    simp [nodeIdeal, completedParameter, toCompleted, Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
    (AdicCompletion.isAdicComplete hfg)

lemma theta_tau_power_mem (r n e : ℕ) (he : r * n ≤ e) :
    tau k r ^ e ∈ completedPower k r n := by
  have hp : tau k r ^ r = completedParameter k r := by
    simp [tau, completedParameter, completedBaseMap, t, parameter, map_pow]
  rw [completedPower, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hp,
    ← pow_mul]
  exact pow_dvd_pow _ he

lemma theta_term_tail (r d j n : ℕ) (hr : 0 < r) (hd : 0 < d) (b : ℤ)
    (hb : b < -((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) ∨
      ((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) < b) :
    thetaTerm k r d j b ∈ completedPower k r n := by
  exact Ideal.mul_mem_right _ _
    (theta_tau_power_mem k r n _ ((theta_exponent_control r d j hr hd).2 n b hb))

lemma theta_partial_stable_ordered (r m d j : ℕ) (nu : ℤ) (hr : 0 < r)
    (hd : 0 < d) (n N M : ℕ) (hN : r * n + 2 * (j + r) + 1 ≤ N)
    (hNM : N ≤ M) :
    thetaPartial k r m d j nu N - thetaPartial k r m d j nu M ∈
      completedPower k r n := by
  classical
  apply Ideal.Quotient.eq.mp
  simp only [thetaPartial, map_sum, apply_ite, map_zero]
  apply Finset.sum_subset
  · intro b hb
    simp only [Finset.mem_Icc] at hb ⊢
    constructor <;> omega
  · intro b hb hbN
    have htail : b < -((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) ∨
        ((r * n + 2 * (j + r) + 1 : ℕ) : ℤ) < b := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hbN
      rcases hbN with hbN | hbN
      · left; omega
      · right; omega
    split_ifs
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (theta_term_tail k r d j n hr hd b htail)
    · rfl

lemma theta_partial_stable (r m d j : ℕ) (nu : ℤ) (hr : 0 < r)
    (hd : 0 < d) (n N M : ℕ) (hN : r * n + 2 * (j + r) + 1 ≤ N)
    (hM : r * n + 2 * (j + r) + 1 ≤ M) :
    thetaPartial k r m d j nu N - thetaPartial k r m d j nu M ∈
      completedPower k r n := by
  rcases le_total N M with h | h
  · exact theta_partial_stable_ordered k r m d j nu hr hd n N M hN h
  · simpa only [neg_sub] using
      (completedPower k r n).neg_mem
        (theta_partial_stable_ordered k r m d j nu hr hd n M N hM h)

theorem theta_completed_limit :
    ∀ (k : Type u) [Field k] [CharZero k] (r m d j : ℕ) (nu : ℤ),
      0 < r → 0 < m → Even m → 0 < d →
      ∃! s : CompletedNode k r, ThetaLimit k r m d j nu s := by
  intro k _ _ r m d j nu hr hm hem hd
  let J : Ideal (CompletedNode k r) := Ideal.span {completedParameter k r}
  let : IsAdicComplete J (CompletedNode k r) := theta_completed_adic k r
  let C : ℕ → ℕ := fun n => r * n + 2 * (j + r) + 1
  let f : ℕ → CompletedNode k r := fun n => thetaPartial k r m d j nu (C n)
  have hf : ∀ {a b : ℕ}, a ≤ b →
      f a ≡ f b [SMOD (J ^ a • ⊤ : Ideal (CompletedNode k r))] := by
    intro a b hab
    rw [SModEq.sub_mem]
    simpa only [smul_eq_mul, Ideal.mul_top, J, completedPower, f] using
      theta_partial_stable k r m d j nu hr hd a (C a) (C b) le_rfl
        (by dsimp [C]; exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left r hab) _) _)
  obtain ⟨s, hs⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J (CompletedNode k r)) hf
  have hs' : ∀ n, s - f n ∈ completedPower k r n := by
    intro n
    have h := hs n
    rw [SModEq.sub_mem] at h
    simpa only [smul_eq_mul, Ideal.mul_top, neg_sub, J, completedPower] using
      (J ^ n • (⊤ : Ideal (CompletedNode k r))).neg_mem h
  have hlimit : ThetaLimit k r m d j nu s := by
    intro n N hN
    have h := (completedPower k r n).add_mem (hs' n)
      (theta_partial_stable k r m d j nu hr hd n (C n) N le_rfl hN)
    simpa only [f, sub_add_sub_cancel] using h
  refine ⟨s, hlimit, ?_⟩
  intro z hz
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  rw [SModEq.sub_mem]
  have h := (completedPower k r n).sub_mem (hz n (C n) le_rfl) (hlimit n (C n) le_rfl)
  simpa only [sub_sub_sub_cancel_right, smul_eq_mul, Ideal.mul_top, J, completedPower] using h

end ArithmeticThetaScaledAnnularR0050
