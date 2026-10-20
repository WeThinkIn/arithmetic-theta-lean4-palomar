module

public import ScaledAnnularDefinitionsR0050
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Jacobson.Ideal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
universe u

namespace ArithmeticThetaScaledAnnularR0050

open ArithmeticThetaScaledTateBridgeR0046

lemma tau_r_eq (k : Type u) [Field k] (r : ℕ) :
    tau k r ^ r = completedParameter k r := by
  change (completedBaseMap k r PowerSeries.X)^r = _
  rw [← map_pow]
  rfl

lemma tau_pow_mul_mem (k : Type u) [Field k] (r n e : ℕ) (z : CompletedNode k r)
    (h : r * n ≤ e) :
    tau k r ^ e * z ∈ completedPower k r n := by
  rw [show e = r * n + (e - r * n) by omega, pow_add]
  have hp : tau k r ^ (r * n) = completedParameter k r ^ n := by
    rw [pow_mul, tau_r_eq]
  rw [hp]
  rw [show completedPower k r n = (Ideal.span {completedParameter k r}) ^ n by rfl]
  rw [Ideal.span_singleton_pow]
  rw [mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma gammaTailFactor_sub_one_mem (k : Type u) [Field k] (r R j l n : ℕ)
    (hL : r * n ≤ gammaLeftExponent R j l)
    (hR : r * n ≤ gammaRightExponent r R j l) :
    gammaTailFactor k r R j l - 1 ∈ completedPower k r n := by
  by_cases hL0 : gammaLeftExponent R j l = 0
  · by_cases hR0 : gammaRightExponent r R j l = 0
    · rw [gammaTailFactor, if_pos hL0, if_pos hR0]
      simp
    · have hB : tau k r ^ gammaRightExponent r R j l * cy k r ∈ completedPower k r n := by
        exact tau_pow_mul_mem k r n _ (cy k r) hR
      have hneg : -(tau k r ^ gammaRightExponent r R j l * cy k r) ∈ completedPower k r n :=
        (completedPower k r n).neg_mem hB
      rw [gammaTailFactor, if_pos hL0, if_neg hR0]
      change (1 * (1 - (tau k r ^ gammaRightExponent r R j l * cy k r))) - 1 ∈
        completedPower k r n
      rw [one_mul]
      simpa only [sub_sub_cancel_left] using hneg
  · by_cases hR0 : gammaRightExponent r R j l = 0
    · have hA : tau k r ^ gammaLeftExponent R j l * cx k r ∈ completedPower k r n := by
        exact tau_pow_mul_mem k r n _ (cx k r) hL
      have hneg : -(tau k r ^ gammaLeftExponent R j l * cx k r) ∈ completedPower k r n :=
        (completedPower k r n).neg_mem hA
      rw [gammaTailFactor, if_neg hL0, if_pos hR0]
      change ((1 - (tau k r ^ gammaLeftExponent R j l * cx k r)) * 1) - 1 ∈
        completedPower k r n
      rw [mul_one]
      simpa only [sub_sub_cancel_left] using hneg
    · have hA : tau k r ^ gammaLeftExponent R j l * cx k r ∈ completedPower k r n := by
        exact tau_pow_mul_mem k r n _ (cx k r) hL
      have hB : tau k r ^ gammaRightExponent r R j l * cy k r ∈ completedPower k r n := by
        exact tau_pow_mul_mem k r n _ (cy k r) hR
      have hAB : (tau k r ^ gammaLeftExponent R j l * cx k r) *
          (tau k r ^ gammaRightExponent r R j l * cy k r) ∈ completedPower k r n :=
        (completedPower k r n).mul_mem_left _ hB
      rw [gammaTailFactor, if_neg hL0, if_neg hR0]
      change ((1 - (tau k r ^ gammaLeftExponent R j l * cx k r)) *
        (1 - (tau k r ^ gammaRightExponent r R j l * cy k r))) - 1 ∈ _
      rw [show ((1 - (tau k r ^ gammaLeftExponent R j l * cx k r)) *
        (1 - (tau k r ^ gammaRightExponent r R j l * cy k r))) - 1 =
        -(tau k r ^ gammaLeftExponent R j l * cx k r) -
          (tau k r ^ gammaRightExponent r R j l * cy k r) +
          (tau k r ^ gammaLeftExponent R j l * cx k r) *
            (tau k r ^ gammaRightExponent r R j l * cy k r) by ring]
      have hsum : -(tau k r ^ gammaLeftExponent R j l * cx k r) -
          (tau k r ^ gammaRightExponent r R j l * cy k r) ∈ completedPower k r n := by
        rw [sub_eq_add_neg]
        exact (completedPower k r n).add_mem ((completedPower k r n).neg_mem hA)
          ((completedPower k r n).neg_mem hB)
      exact (completedPower k r n).add_mem hsum hAB

lemma gammaTailFactor_sub_one_mem_later (k : Type u) [Field k] (r R j l n : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) (hl : n ≤ l) :
    gammaTailFactor k r R j l - 1 ∈ completedPower k r n := by
  by_cases hn : n = 0
  · subst n
    simp [completedPower]
  apply gammaTailFactor_sub_one_mem
  · have hRpos : 0 < R := by omega
    have hrR : r ≤ R := by omega
    have hmulR : r * l ≤ R * l := Nat.mul_le_mul_right l hrR
    change r * n ≤ R * l + j
    exact (le_trans (Nat.mul_le_mul_left r hl) hmulR).trans (Nat.le_add_right _ _)
  · have hRpos : 0 < R := by omega
    have hrR : r ≤ R := by omega
    have hmulR : r * l ≤ R * l := Nat.mul_le_mul_right l hrR
    change r * n ≤ R * (l + 1) - j - r
    rw [Nat.mul_succ]
    have hright : R * l ≤ R * l + R - j - r := by omega
    exact (le_trans (Nat.mul_le_mul_left r hl) hmulR).trans hright

lemma gammaTailLater_prod_smodEq_one (k : Type u) [Field k] (r R j m q : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) :
    (∏ x ∈ Finset.range q, gammaTailFactor k r R j (m + x)) ≡ 1
      [SMOD (completedPower k r m)] := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.prod_range_succ]
      have hf : gammaTailFactor k r R j (m + q) ≡ 1
          [SMOD (completedPower k r m)] := by
        apply SModEq.sub_mem.mpr
        exact gammaTailFactor_sub_one_mem_later k r R j (m + q) m hr hj
          (Nat.le_add_right m q)
      simpa using (SModEq.mul ih hf)

lemma gammaTailPartial_smodEq (k : Type u) [Field k] (r R j m N : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) (hmN : m ≤ N) :
    gammaTailPartial k r R j m ≡ gammaTailPartial k r R j N
      [SMOD (completedPower k r m)] := by
  have hdecomp : gammaTailPartial k r R j N =
      gammaTailPartial k r R j m *
        (∏ x ∈ Finset.range (N - m), gammaTailFactor k r R j (m + x)) := by
    change (∏ x ∈ Finset.range N, gammaTailFactor k r R j x) =
      (∏ x ∈ Finset.range m, gammaTailFactor k r R j x) *
        (∏ x ∈ Finset.range (N - m), gammaTailFactor k r R j (m + x))
    rw [show N = m + (N - m) by omega, Finset.prod_range_add]
    rw [show m + (N - m) - m = N - m by omega]
  rw [hdecomp]
  have hprod := gammaTailLater_prod_smodEq_one k r R j m (N - m) hr hj
  have hmul := SModEq.mul (SModEq.refl (gammaTailPartial k r R j m)) hprod
  simpa [mul_one] using hmul.symm

lemma gammaFactor_eq_tail_later (k : Type u) [Field k] (r R j l : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) (hl : 0 < l) :
    gammaFactor k r R j l = gammaTailFactor k r R j l := by
  have hR : 0 < R := by omega
  have hL : gammaLeftExponent R j l ≠ 0 := by
    simp [gammaLeftExponent]
    omega
  have hRt : gammaRightExponent r R j l ≠ 0 := by
    have hRl : R ≤ R * l := Nat.le_mul_of_pos_right R hl
    have hlt : j + r < R * (l + 1) := by
      rw [Nat.mul_succ]
      omega
    have hpos : 0 < R * (l + 1) - j - r := by omega
    exact Nat.ne_of_gt (by simpa [gammaRightExponent] using hpos)
  simp [gammaFactor, gammaTailFactor, hL, hRt]

lemma gammaFactor_zero_decomp (k : Type u) [Field k] (r R j : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) :
    gammaFactor k r R j 0 = gammaHorizontal k r R j * gammaTailFactor k r R j 0 := by
  by_cases hJ : j = 0
  · by_cases hJR : j + r = R
    · have hz : R - j - r = 0 := by omega
      subst j
      have hrR : r = R := by omega
      simp [gammaFactor, gammaTailFactor, gammaHorizontal, gammaLeftExponent,
        gammaRightExponent, hz, hrR, hJR] <;> ring
    · have hz : R - j - r ≠ 0 := by omega
      subst j
      have hrR : r ≠ R := by omega
      have hz' : R - r ≠ 0 := by simpa using hz
      simp [gammaFactor, gammaTailFactor, gammaHorizontal, gammaLeftExponent,
        gammaRightExponent, hz', hrR, hJR] <;> ring
  · by_cases hJR : j + r = R
    · have hz : R - j - r = 0 := by omega
      simp [gammaFactor, gammaTailFactor, gammaHorizontal, gammaLeftExponent,
        gammaRightExponent, hJ, hz, hJR] <;> ring
    · have hz : R - j - r ≠ 0 := by omega
      simp [gammaFactor, gammaTailFactor, gammaHorizontal, gammaLeftExponent,
        gammaRightExponent, hJ, hz, hJR] <;> ring

lemma gammaPartial_eq_horizontal_mul_tail (k : Type u) [Field k] (r R j N : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) (hN : 1 ≤ N) :
    gammaPartial k r R j N = gammaHorizontal k r R j * gammaTailPartial k r R j N := by
  rw [gammaPartial, gammaTailPartial, show N = 1 + (N - 1) by omega,
    Finset.prod_range_add]
  have hprod : (∏ x ∈ Finset.range (N - 1), gammaFactor k r R j (1 + x)) =
      ∏ x ∈ Finset.range (N - 1), gammaTailFactor k r R j (1 + x) := by
    apply Finset.prod_congr rfl
    intro x hx
    apply gammaFactor_eq_tail_later k r R j (1 + x) hr hj
    simp at hx ⊢
  simp only [Finset.prod_range_one]
  rw [gammaFactor_zero_decomp k r R j hr hj, hprod]
  rw [← show 1 + (N - 1) = N by omega, Finset.prod_range_add]
  rw [show 1 + (N - 1) - 1 = N - 1 by omega]
  simp only [Finset.prod_range_one]
  ring

lemma tail_factor_isUnit (k : Type u) [Field k] [CharZero k] (r R j l : ℕ)
    (hr : 0 < r) (hj : j + r ≤ R) (hjac : completedPower k r 1 ≤
      (⊥ : Ideal (CompletedNode k r)).jacobson) :
    IsUnit (gammaTailFactor k r R j l) := by
  have hunit_sub (e : ℕ) (z : CompletedNode k r) (he : 0 < e) :
      IsUnit (1 - tau k r ^ e * z) := by
    have hpow : (tau k r ^ e * z) ^ r ∈ completedPower k r 1 := by
      rw [mul_pow]
      rw [← pow_mul]
      apply tau_pow_mul_mem k r 1 (e * r) (z ^ r)
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right r (Nat.succ_le_iff.mp he)
    have hrad : (tau k r ^ e * z) ∈ (⊥ : Ideal (CompletedNode k r)).jacobson := by
      exact (Ideal.isRadical_jacobson (⊥ : Ideal (CompletedNode k r)))
        (Ideal.mem_radical_of_pow_mem (Ideal.le_radical (hjac hpow)))
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa [sub_eq_add_neg] using ((⊥ : Ideal (CompletedNode k r)).jacobson.neg_mem hrad)
  have hleft : IsUnit (if gammaLeftExponent R j l = 0 then (1 : CompletedNode k r)
      else 1 - tau k r ^ gammaLeftExponent R j l * cx k r) := by
    split_ifs with h
    · exact isUnit_one
    · exact hunit_sub _ _ (Nat.pos_of_ne_zero h)
  have hright : IsUnit (if gammaRightExponent r R j l = 0 then (1 : CompletedNode k r)
      else 1 - tau k r ^ gammaRightExponent r R j l * cy k r) := by
    split_ifs with h
    · exact isUnit_one
    · exact hunit_sub _ _ (Nat.pos_of_ne_zero h)
  exact hleft.mul hright

theorem gamma_unit_product :
    ∀ (k : Type u) [Field k] [CharZero k] (r R j : ℕ), 0 < r → j + r ≤ R →
      ∃! u : CompletedNode k r, IsUnit u ∧
        (∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          u - gammaTailPartial k r R j N ∈ completedPower k r n) ∧
        (∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          gammaHorizontal k r R j * u - gammaPartial k r R j N ∈ completedPower k r n) := by
  intro k _ _ r R j hr hj
  let J : Ideal (CompletedNode k r) := completedPower k r 1
  letI : IsAdicComplete (nodeIdeal k r) (CompletedNode k r) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r)))
      (CompletedNode k r) := by
    exact (IsAdicComplete.map_algebraMap_iff (nodeIdeal k r)
      (CompletedNode k r)).mpr inferInstance
  have hpow (n : ℕ) : completedPower k r n =
      ((nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r))) ^ n := by
    simp [completedPower, nodeIdeal, completedParameter, toCompleted, Ideal.map_span]
  have hJ : J = (nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r)) := by
    simpa [J] using hpow 1
  have hJjac : J ≤ (⊥ : Ideal (CompletedNode k r)).jacobson := by
    rw [hJ]
    exact IsAdicComplete.le_jacobson_bot _
  have hcauchy : ∀ {m N : ℕ}, m ≤ N →
      gammaTailPartial k r R j m ≡ gammaTailPartial k r R j N
        [SMOD (((nodeIdeal k r).map
          (algebraMap (Node k r) (CompletedNode k r))) ^ m •
          (⊤ : Submodule (CompletedNode k r) (CompletedNode k r)))] := by
    intro m N hmN
    have hs := gammaTailPartial_smodEq k r R j m N hr hj hmN
    rw [SModEq.sub_mem] at hs
    rw [SModEq.sub_mem]
    simpa [hpow, smul_eq_mul, Ideal.mul_top] using hs
  obtain ⟨u, hu⟩ := hcomp.2.prec hcauchy
  have hu_mem (n N : ℕ) (hN : n ≤ N) :
      u - gammaTailPartial k r R j N ∈ completedPower k r n := by
    have h := hu N
    rw [SModEq.sub_mem] at h
    rw [← hpow N] at h
    have hneg := ((completedPower k r N) •
      (⊤ : Submodule (CompletedNode k r) (CompletedNode k r))).neg_mem h
    have hneg' : u - gammaTailPartial k r R j N ∈ completedPower k r N := by
      simpa [J, smul_eq_mul, Ideal.mul_top] using hneg
    exact (Ideal.pow_le_pow_right hN) hneg'
  have htail_unit (N : ℕ) : IsUnit (gammaTailPartial k r R j N) := by
    rw [gammaTailPartial]
    rw [IsUnit.prod_iff]
    intro l hl
    exact tail_factor_isUnit k r R j l hr hj hJjac
  have hunit_sub_limit {a b : CompletedNode k r} (hb : IsUnit b)
      (hab : a - b ∈ J) : IsUnit a := by
    rcases hb with ⟨V, rfl⟩
    let w : CompletedNode k r := (↑(V⁻¹) : CompletedNode k r) * (a - (V : CompletedNode k r))
    have hw : w ∈ (⊥ : Ideal (CompletedNode k r)).jacobson := by
      exact (Ideal.mul_mem_left _ _ (hJjac hab))
    have hwunit : IsUnit (1 + w) := by
      apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
      simpa [w] using hw
    have heq : (V : CompletedNode k r) * (1 + w) = a := by
      dsimp [w]
      calc
        (V : CompletedNode k r) *
            (1 + (↑(V⁻¹) : CompletedNode k r) * (a - (V : CompletedNode k r))) =
            (V : CompletedNode k r) +
              ((V : CompletedNode k r) * (↑(V⁻¹) : CompletedNode k r)) *
                (a - (V : CompletedNode k r)) := by ring
        _ = a := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← heq]
    exact IsUnit.mul (Units.isUnit V) hwunit
  have hu_unit : IsUnit u := by
    have h := hu_mem 1 1 (le_refl _)
    exact hunit_sub_limit (htail_unit 1) (by simpa [J] using h)
  have hmain : IsUnit u ∧
      (∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        u - gammaTailPartial k r R j N ∈ completedPower k r n) ∧
      (∀ n : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        gammaHorizontal k r R j * u - gammaPartial k r R j N ∈ completedPower k r n) := by
    refine ⟨hu_unit, ?_, ?_⟩
    · intro n
      exact ⟨n, fun N hN => hu_mem n N hN⟩
    · intro n
      refine ⟨max n 1, ?_⟩
      intro N hN
      have h1N : 1 ≤ N := le_trans (Nat.le_max_right n 1) hN
      rw [gammaPartial_eq_horizontal_mul_tail k r R j N hr hj h1N]
      rw [← mul_sub]
      exact (completedPower k r n).mul_mem_left _
        (hu_mem n N (le_trans (Nat.le_max_left _ _) hN))
  refine ⟨u, hmain, ?_⟩
  intro v hv
  letI : IsHausdorff
      ((nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r)))
      (CompletedNode k r) := hcomp.1
  apply (IsHausdorff.eq_iff_smodEq
    (I := (nodeIdeal k r).map (algebraMap (Node k r) (CompletedNode k r)))
    (M := CompletedNode k r)).mpr
  intro n
  rw [SModEq.sub_mem]
  rcases hv.2.1 n with ⟨N₀, hN₀⟩
  let N := max N₀ n
  have hu' := hu_mem n N (Nat.le_max_right _ _)
  have hv' : v - gammaTailPartial k r R j N ∈ completedPower k r n := by
    exact hN₀ N (Nat.le_max_left _ _)
  have hdiff : u - v ∈ completedPower k r n := by
    have htmp := (completedPower k r n).sub_mem hu' hv'
    convert htmp using 1 <;> ring
  have hdiff' := (completedPower k r n).neg_mem hdiff
  simpa [J, hpow, smul_eq_mul, Ideal.mul_top, sub_eq_add_neg] using hdiff'

end ArithmeticThetaScaledAnnularR0050
