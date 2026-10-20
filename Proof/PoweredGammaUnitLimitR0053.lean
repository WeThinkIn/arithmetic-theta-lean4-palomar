module

public import AnnularTorsionPrerequisiteDefinitionsR0053

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

private lemma rightExponent_dvd (r c j l : ℕ) (hc : c ∣ r) :
    (c : ℤ) ∣ rightExponent r c j l := by
  rcases hc with ⟨d, rfl⟩
  refine ⟨(d : ℤ) * ((l : ℤ) + 1) - ((j : ℤ) + 1), ?_⟩
  simp only [rightExponent, Nat.cast_mul]
  ring

private lemma rightExponent_negative_gap (r c j l : ℕ) (hc : c ∣ r)
    (hc0 : 0 < c) (he : rightExponent r c j l < 0) :
    rightExponent r c j l ≤ -(c : ℤ) := by
  rcases rightExponent_dvd r c j l hc with ⟨z, hz⟩
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc0
  have hzneg : z ≤ -1 := by
    by_contra h
    have hz0 : 0 ≤ z := by omega
    have := mul_nonneg (le_of_lt hcz) hz0
    omega
  have hbound := mul_nonneg (le_of_lt hcz) (show (0 : ℤ) ≤ -z - 1 by omega)
  rw [hz] at he ⊢
  nlinarith

private lemma large_exponents (r c j l n : ℕ) (hr : 0 < r)
    (hl : cutoff c j n ≤ l) :
    n ≤ leftExponent r c j l ∧
      (n : ℤ) ≤ rightExponent r c j l := by
  have hrl : l ≤ r * l := by
    calc
      l = 1 * l := by omega
      _ ≤ r * l := Nat.mul_le_mul_right l hr
  have hrl' : l + 1 ≤ r * (l + 1) := by
    calc
      l + 1 = 1 * (l + 1) := by omega
      _ ≤ r * (l + 1) := Nat.mul_le_mul_right (l + 1) hr
  constructor
  · dsimp [leftExponent, cutoff] at *
    omega
  · dsimp [rightExponent, cutoff] at *
    have hcast : (l + 1 : ℤ) ≤ (r : ℤ) * ((l : ℤ) + 1) := by
      exact_mod_cast hrl'
    have hcast' : (n + c * (j + 1) + c + 1 : ℤ) ≤ l := by
      exact_mod_cast hl
    omega

private lemma tailFactor_sub_one_mem_later
    (k : Type u) [Field k] [CharZero k] (r c j l n : ℕ)
    (hr : 0 < r) (hn : 0 < n) (hl : cutoff c j n ≤ l) :
    tailFactor k r c j l - 1 ∈ filtration k n := by
  obtain ⟨hL, hR⟩ := large_exponents r c j l n hr hl
  have hL0 : leftExponent r c j l ≠ 0 := by omega
  have hR0 : ¬ rightExponent r c j l < 0 := by omega
  have hR1 : rightExponent r c j l ≠ 0 := by omega
  let e : ℕ := (rightExponent r c j l).toNat
  have he : n ≤ e := by
    dsimp [e]
    omega
  have hA : tau k ^ leftExponent r c j l * cx k ^ c ∈ filtration k n := by
    exact ArithmeticThetaScaledAnnularR0050.tau_pow_mul_mem k 1 n
      (leftExponent r c j l) (cx k ^ c) (by simpa using hL)
  have hB : tau k ^ e * cy k ^ c ∈ filtration k n := by
    exact ArithmeticThetaScaledAnnularR0050.tau_pow_mul_mem k 1 n e
      (cy k ^ c) (by simpa using he)
  have hAB : (tau k ^ leftExponent r c j l * cx k ^ c) *
      (tau k ^ e * cy k ^ c) ∈ filtration k n :=
    (filtration k n).mul_mem_left _ hB
  have hsum : -(tau k ^ leftExponent r c j l * cx k ^ c) -
      (tau k ^ e * cy k ^ c) ∈ filtration k n := by
    rw [sub_eq_add_neg]
    exact (filtration k n).add_mem ((filtration k n).neg_mem hA)
      ((filtration k n).neg_mem hB)
  have hid : tailFactor k r c j l =
      (1 - tau k ^ leftExponent r c j l * cx k ^ c) *
        (1 - tau k ^ e * cy k ^ c) := by
    simp [tailFactor, tailRight, hL0, hR0, hR1, e]
  rw [hid]
  convert (filtration k n).add_mem hsum hAB using 1 <;> ring

private lemma tailFactor_sub_one_mem_at_cutoff
    (k : Type u) [Field k] [CharZero k] (r c j l n : ℕ)
    (hr : 0 < r) (hl : cutoff c j n ≤ l) :
    tailFactor k r c j l - 1 ∈ filtration k n := by
  by_cases hn : n = 0
  · subst n
    simp [filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower]
  · exact tailFactor_sub_one_mem_later k r c j l n hr (Nat.pos_of_ne_zero hn) hl

private lemma tailLater_prod_smodEq_one
    (k : Type u) [Field k] [CharZero k] (r c j n m q : ℕ)
    (hr : 0 < r) (hm : cutoff c j n ≤ m) :
    (∏ x ∈ Finset.range q, tailFactor k r c j (m + x)) ≡ 1
      [SMOD (filtration k n)] := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.prod_range_succ]
      have hf : tailFactor k r c j (m + q) ≡ 1
          [SMOD (filtration k n)] := by
        apply SModEq.sub_mem.mpr
        exact tailFactor_sub_one_mem_at_cutoff k r c j (m + q) n hr
          (le_trans hm (Nat.le_add_right m q))
      simpa using SModEq.mul ih hf

private lemma tailPartial_smodEq
    (k : Type u) [Field k] [CharZero k] (r c j n m N : ℕ)
    (hr : 0 < r) (hm : cutoff c j n ≤ m) (hmN : m ≤ N) :
    tailPartial k r c j m ≡ tailPartial k r c j N
      [SMOD (filtration k n)] := by
  have hdecomp : tailPartial k r c j N =
      tailPartial k r c j m *
        (∏ x ∈ Finset.range (N - m), tailFactor k r c j (m + x)) := by
    change (∏ x ∈ Finset.range N, tailFactor k r c j x) =
      (∏ x ∈ Finset.range m, tailFactor k r c j x) *
        (∏ x ∈ Finset.range (N - m), tailFactor k r c j (m + x))
    rw [show N = m + (N - m) by omega, Finset.prod_range_add]
    rw [show m + (N - m) - m = N - m by omega]
  rw [hdecomp]
  have hprod := tailLater_prod_smodEq_one k r c j n m (N - m) hr hm
  have hmul := SModEq.mul (SModEq.refl (tailPartial k r c j m)) hprod
  simpa [mul_one] using hmul.symm

private lemma tail_factor_isUnit
    (k : Type u) [Field k] [CharZero k] (r c j l : ℕ)
    (hc : c ∣ r) (hc0 : 0 < c)
    (hjac : filtration k 1 ≤ (⊥ : Ideal (Chart k)).jacobson) :
    IsUnit (tailFactor k r c j l) := by
  have hunit_sub (e : ℕ) (z : Chart k) (he : 0 < e) :
      IsUnit (1 - tau k ^ e * z) := by
    have hmem : tau k ^ e * z ∈ filtration k 1 := by
      exact ArithmeticThetaScaledAnnularR0050.tau_pow_mul_mem k 1 1 e z
        (by omega)
    have hrad : tau k ^ e * z ∈ (⊥ : Ideal (Chart k)).jacobson := hjac hmem
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa [sub_eq_add_neg] using
      ((⊥ : Ideal (Chart k)).jacobson.neg_mem hrad)
  have hleft : IsUnit (if leftExponent r c j l = 0 then (1 : Chart k)
      else 1 - tau k ^ leftExponent r c j l * cx k ^ c) := by
    split_ifs with h
    · exact isUnit_one
    · exact hunit_sub _ _ (Nat.pos_of_ne_zero h)
  have hright : IsUnit (tailRight k r c j l) := by
    by_cases he : rightExponent r c j l < 0
    · by_cases hz : -rightExponent r c j l - (c : ℤ) = 0
      · simpa [tailRight, he, hz] using (isUnit_one : IsUnit (1 : Chart k))
      · have hgap := rightExponent_negative_gap r c j l hc hc0 he
        have hpos : 0 < (-rightExponent r c j l - (c : ℤ)).toNat := by omega
        simpa [tailRight, he, hz] using
          (hunit_sub _ (cx k ^ c) hpos)
    · by_cases hz : rightExponent r c j l = 0
      · simpa [tailRight, he, hz] using (isUnit_one : IsUnit (1 : Chart k))
      · have hpos : 0 < (rightExponent r c j l).toNat := by omega
        simpa [tailRight, he, hz] using
          (hunit_sub _ (cy k ^ c) hpos)
  change IsUnit ((if leftExponent r c j l = 0 then (1 : Chart k)
    else 1 - tau k ^ leftExponent r c j l * cx k ^ c) * tailRight k r c j l)
  exact hleft.mul hright

private theorem tailLimit_exists
    (k : Type u) [Field k] [CharZero k] (r c j : ℕ)
    (hr : 0 < r) (hc : c ∣ r) (hc0 : 0 < c) :
    ∃ v : Chart k, IsUnit v ∧ ∀ n N : ℕ,
      cutoff c j n ≤ N → v - tailPartial k r c j N ∈ filtration k n := by
  let J : Ideal (Chart k) := filtration k 1
  letI : IsAdicComplete
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k)).mpr inferInstance
  have hpow (n : ℕ) : filtration k n =
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) ^ n := by
    simp [filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
  have hJ : J = (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (Node k) (Chart k)) := by
    simpa [J] using hpow 1
  have hJjac : J ≤ (⊥ : Ideal (Chart k)).jacobson := by
    rw [hJ]
    exact IsAdicComplete.le_jacobson_bot _
  let f : ℕ → Chart k := fun m => tailPartial k r c j (cutoff c j m)
  have hcauchy : ∀ {m N : ℕ}, m ≤ N →
      f m ≡ f N
        [SMOD (((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
          (algebraMap (Node k) (Chart k))) ^ m •
          (⊤ : Submodule (Chart k) (Chart k)))] := by
    intro m N hmN
    have hcut : cutoff c j m ≤ cutoff c j N := by
      dsimp [cutoff]
      omega
    have hs := tailPartial_smodEq k r c j m (cutoff c j m)
      (cutoff c j N) hr (le_refl _) hcut
    rw [SModEq.sub_mem] at hs
    rw [SModEq.sub_mem]
    simpa [f, hpow, smul_eq_mul, Ideal.mul_top] using hs
  obtain ⟨v, hv⟩ := hcomp.2.prec hcauchy
  have hv_mem (n N : ℕ) (hN : cutoff c j n ≤ N) :
      v - tailPartial k r c j N ∈ filtration k n := by
    have h := hv n
    rw [SModEq.sub_mem] at h
    rw [← hpow n] at h
    have hneg := ((filtration k n) •
      (⊤ : Submodule (Chart k) (Chart k))).neg_mem h
    have hfirst : v - f n ∈ filtration k n := by
      simpa [smul_eq_mul, Ideal.mul_top] using hneg
    have hsecond := tailPartial_smodEq k r c j n (cutoff c j n) N
      hr (le_refl _) hN
    rw [SModEq.sub_mem] at hsecond
    have hsum := (filtration k n).add_mem hfirst hsecond
    convert hsum using 1 <;> simp [f] <;> ring
  have htail_unit (N : ℕ) : IsUnit (tailPartial k r c j N) := by
    rw [tailPartial, IsUnit.prod_iff]
    intro l hl
    exact tail_factor_isUnit k r c j l hc hc0 (by simpa [J] using hJjac)
  have hunit_sub_limit {a b : Chart k} (hb : IsUnit b)
      (hab : a - b ∈ J) : IsUnit a := by
    rcases hb with ⟨V, rfl⟩
    let w : Chart k := (↑(V⁻¹) : Chart k) * (a - (V : Chart k))
    have hw : w ∈ (⊥ : Ideal (Chart k)).jacobson := by
      exact Ideal.mul_mem_left _ _ (hJjac hab)
    have hwunit : IsUnit (1 + w) := by
      apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
      simpa [w] using hw
    have heq : (V : Chart k) * (1 + w) = a := by
      dsimp [w]
      calc
        (V : Chart k) * (1 + (↑(V⁻¹) : Chart k) * (a - (V : Chart k))) =
            (V : Chart k) +
              ((V : Chart k) * (↑(V⁻¹) : Chart k)) *
                (a - (V : Chart k)) := by ring
        _ = a := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← heq]
    exact IsUnit.mul (Units.isUnit V) hwunit
  have hv_unit : IsUnit v := by
    have h := hv_mem 1 (cutoff c j 1) (le_refl _)
    exact hunit_sub_limit (htail_unit (cutoff c j 1)) (by simpa [J] using h)
  exact ⟨v, hv_unit, hv_mem⟩

private def exceptionalLeft (k : Type u) [Field k] (r c j l : ℕ) : Chart k :=
  if leftExponent r c j l = 0 then 1 - cx k ^ c else 1

private def exceptionalRight (k : Type u) [Field k] (r c j l : ℕ) : Chart k :=
  if rightExponent r c j l = -(c : ℤ) then 1 - cx k ^ c
  else if rightExponent r c j l = 0 then 1 - cy k ^ c else 1

private def exceptionalFactor (k : Type u) [Field k] (r c j l : ℕ) : Chart k :=
  exceptionalLeft k r c j l * exceptionalRight k r c j l

private lemma normalizedRight_eq_exceptional_mul_tail
    (k : Type u) [Field k] (r c j l : ℕ) (hc0 : 0 < c) :
    normalizedRight k r c j l =
      exceptionalRight k r c j l * tailRight k r c j l := by
  let e := rightExponent r c j l
  by_cases hneg : e < 0
  · by_cases hz : -e - (c : ℤ) = 0
    · have heq : e = -(c : ℤ) := by omega
      simp [normalizedRight, exceptionalRight, tailRight, e, hneg, hz, heq, hc0]
    · have hne : e ≠ -(c : ℤ) := by omega
      have hne0 : e ≠ 0 := by omega
      simp [normalizedRight, exceptionalRight, tailRight, e, hneg, hz, hne, hne0]
  · have hne : e ≠ -(c : ℤ) := by omega
    by_cases hz : e = 0
    · simp [normalizedRight, exceptionalRight, tailRight, e, hneg, hne, hz, hc0.ne']
    · simp [normalizedRight, exceptionalRight, tailRight, e, hneg, hne, hz]

private lemma normalizedFactor_eq_exceptional_mul_tail
    (k : Type u) [Field k] (r c j l : ℕ) (hc0 : 0 < c) :
    normalizedFactor k r c j l =
      exceptionalFactor k r c j l * tailFactor k r c j l := by
  have hright := normalizedRight_eq_exceptional_mul_tail k r c j l hc0
  by_cases hz : leftExponent r c j l = 0
  · simp [normalizedFactor, exceptionalFactor, exceptionalLeft, tailFactor, hz,
      hright]
    ring
  · simp [normalizedFactor, exceptionalFactor, exceptionalLeft, tailFactor, hz,
      hright]
    ring

private lemma normalizedPartial_eq_exceptional_mul_tail
    (k : Type u) [Field k] (r c j N : ℕ) (hc0 : 0 < c) :
    normalizedPartial k r c j N =
      (∏ l ∈ Finset.range N, exceptionalFactor k r c j l) *
        tailPartial k r c j N := by
  simp only [normalizedPartial, tailPartial]
  conv_lhs => arg 2; ext l; rw [normalizedFactor_eq_exceptional_mul_tail k r c j l hc0]
  exact Finset.prod_mul_distrib

private lemma rightExponent_eq_neg_c_iff (r c j l : ℕ) :
    rightExponent r c j l = -(c : ℤ) ↔ r * (l + 1) = c * j := by
  change (r : ℤ) * ((l : ℤ) + 1) - (c : ℤ) * ((j : ℤ) + 1) = -(c : ℤ) ↔ _
  constructor
  · intro h
    have h' : (r : ℤ) * ((l : ℤ) + 1) = (c : ℤ) * j := by nlinarith
    have : ((r * (l + 1) : ℕ) : ℤ) = ((c * j : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h'
    exact_mod_cast this
  · intro h
    have h' : (r : ℤ) * ((l : ℤ) + 1) = (c : ℤ) * j := by exact_mod_cast h
    nlinarith

private lemma rightExponent_eq_zero_iff (r c j l : ℕ) :
    rightExponent r c j l = 0 ↔ r * (l + 1) = c * (j + 1) := by
  change (r : ℤ) * ((l : ℤ) + 1) - (c : ℤ) * ((j : ℤ) + 1) = 0 ↔ _
  constructor
  · intro h
    have h' : (r : ℤ) * ((l : ℤ) + 1) = (c : ℤ) * ((j : ℤ) + 1) := by omega
    exact_mod_cast h'
  · intro h
    have h' : (r : ℤ) * ((l : ℤ) + 1) = (c : ℤ) * ((j : ℤ) + 1) := by exact_mod_cast h
    omega

private lemma unique_index (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (hdiv : r ∣ m) :
    ∃ q : ℕ, r * (q + 1) = m ∧
      ∀ l : ℕ, r * (l + 1) = m → l = q := by
  rcases hdiv with ⟨a, rfl⟩
  have ha : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    simp [this] at hm
  refine ⟨a - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (by omega)]
  · intro l hl
    have hcancel : l + 1 = a := by
      exact Nat.eq_of_mul_eq_mul_left hr hl
    omega

private lemma exceptionalLeft_prod
    (k : Type u) [Field k] (r c j N : ℕ) (hr : 0 < r) (hc0 : 0 < c)
    (hN : 0 < N) :
    (∏ l ∈ Finset.range N, exceptionalLeft k r c j l) =
      if j = 0 then 1 - cx k ^ c else 1 := by
  by_cases hj : j = 0
  · subst j
    rw [Finset.prod_eq_single_of_mem 0 (Finset.mem_range.mpr hN)]
    · simp [exceptionalLeft, leftExponent]
    · intro l hl hne
      have hl : 0 < l := Nat.pos_of_ne_zero hne
      have hpos : 0 < leftExponent r c 0 l := by
        simp only [leftExponent, mul_zero, add_zero]
        exact Nat.mul_pos hr hl
      simp [exceptionalLeft, hpos.ne']
  · have hnone : ∀ l : ℕ, leftExponent r c j l ≠ 0 := by
      intro l
      simp only [leftExponent]
      have hj0 : 0 < c * j := Nat.mul_pos hc0 (Nat.pos_of_ne_zero hj)
      omega
    simp [exceptionalLeft, hnone, hj]

private lemma exceptionalRight_split
    (k : Type u) [Field k] (r c j l : ℕ) (hc0 : 0 < c) :
    exceptionalRight k r c j l =
      (if r * (l + 1) = c * j then 1 - cx k ^ c else 1) *
      (if r * (l + 1) = c * (j + 1) then 1 - cy k ^ c else 1) := by
  have hdisj : ¬ (r * (l + 1) = c * j ∧ r * (l + 1) = c * (j + 1)) := by
    intro ⟨h1, h2⟩
    have : c * j = c * (j + 1) := h1.symm.trans h2
    have := Nat.eq_of_mul_eq_mul_left hc0 this
    omega
  by_cases hx : r * (l + 1) = c * j
  · have hy : r * (l + 1) ≠ c * (j + 1) := by tauto
    have hcne : c ≠ 0 := Nat.ne_of_gt hc0
    simp [exceptionalRight, rightExponent_eq_neg_c_iff, rightExponent_eq_zero_iff,
      hx, hy, hcne]
  · by_cases hy : r * (l + 1) = c * (j + 1)
    · have hcne : c ≠ 0 := Nat.ne_of_gt hc0
      simp [exceptionalRight, rightExponent_eq_neg_c_iff,
        rightExponent_eq_zero_iff, hx, hy, hcne]
    · simp [exceptionalRight, rightExponent_eq_neg_c_iff,
        rightExponent_eq_zero_iff, hx, hy]

private lemma product_at_unique_index
    (k : Type u) [Field k] (r m N : ℕ) (z : Chart k)
    (hr : 0 < r) (hN : m < N) :
    (∏ l ∈ Finset.range N, if r * (l + 1) = m then z else 1) =
      if r ∣ m ∧ 0 < m then z else 1 := by
  by_cases h : r ∣ m ∧ 0 < m
  · obtain ⟨q, hq, huniq⟩ := unique_index r m hr h.2 h.1
    have hqN : q < N := by
      have hqle : q < m := by
        have : q + 1 ≤ r * (q + 1) := by
          calc
            q + 1 = 1 * (q + 1) := by omega
            _ ≤ r * (q + 1) := Nat.mul_le_mul_right _ hr
        omega
      omega
    rw [Finset.prod_eq_single_of_mem q (Finset.mem_range.mpr hqN)]
    · simp [hq, h]
    · intro l hl hne
      have hneq : r * (l + 1) ≠ m := by
        intro heq
        exact hne (huniq l heq)
      simp [hneq]
  · have hnone : ∀ l : ℕ, r * (l + 1) ≠ m := by
      intro l heq
      apply h
      constructor
      · exact ⟨l + 1, heq.symm⟩
      · rw [← heq]
        exact Nat.mul_pos hr (Nat.succ_pos l)
    simp [hnone, h]

private lemma exceptionalRight_prod
    (k : Type u) [Field k] (r c j N : ℕ)
    (hr : 0 < r) (hc0 : 0 < c) (hN : c * (j + 1) < N) :
    (∏ l ∈ Finset.range N, exceptionalRight k r c j l) =
      (if 0 < j ∧ r ∣ c * j then 1 - cx k ^ c else 1) *
      (if r ∣ c * (j + 1) then 1 - cy k ^ c else 1) := by
  conv_lhs => arg 2; ext l; rw [exceptionalRight_split k r c j l hc0]
  rw [Finset.prod_mul_distrib]
  have hxN : c * j < N := by
    have : c * j < c * (j + 1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self j) hc0
    omega
  rw [product_at_unique_index k r (c * j) N (1 - cx k ^ c) hr hxN]
  rw [product_at_unique_index k r (c * (j + 1)) N (1 - cy k ^ c) hr hN]
  have hypos : 0 < c * (j + 1) := Nat.mul_pos hc0 (Nat.succ_pos j)
  by_cases hj : j = 0
  · subst j
    simp [hc0]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hxpos : 0 < c * j := Nat.mul_pos hc0 hjpos
    simp [hjpos, hxpos, hypos]

private lemma exceptionalFactor_prod
    (k : Type u) [Field k] (r c j N : ℕ)
    (hr : 0 < r) (hc0 : 0 < c) (hN : c * (j + 1) < N) :
    (∏ l ∈ Finset.range N, exceptionalFactor k r c j l) =
      horizontal k r c j := by
  conv_lhs => arg 2; ext l; rw [exceptionalFactor]
  rw [Finset.prod_mul_distrib]
  have hN0 : 0 < N := by omega
  rw [exceptionalLeft_prod k r c j N hr hc0 hN0]
  rw [exceptionalRight_prod k r c j N hr hc0 hN]
  by_cases hj : j = 0
  · subst j
    simp [horizontal, horizontalEquation, coord]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    simp [horizontal, horizontalEquation, coord, hjpos, hj]

private lemma normalizedPartial_eq_horizontal_mul_tail
    (k : Type u) [Field k] (r c j N : ℕ)
    (hr : 0 < r) (hc0 : 0 < c) (hN : c * (j + 1) < N) :
    normalizedPartial k r c j N =
      horizontal k r c j * tailPartial k r c j N := by
  rw [normalizedPartial_eq_exceptional_mul_tail k r c j N hc0]
  rw [exceptionalFactor_prod k r c j N hr hc0 hN]

theorem powered_gamma_unit_limit :
    ∀ (k : Type u) [Field k] [CharZero k] (r c j : ℕ),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 → j < r →
      ∃! v : Chart k, IsUnit v ∧
        ∀ n N : ℕ, cutoff c j n ≤ N →
          v - tailPartial k r c j N ∈ filtration k n ∧
          horizontal k r c j * v - normalizedPartial k r c j N ∈ filtration k n := by
  intro k _ _ r c j hr hc1 hc _ _
  have hc0 : 0 < c := by omega
  obtain ⟨v, hv_unit, hv_tail⟩ := tailLimit_exists k r c j hr hc hc0
  have hv_main : IsUnit v ∧ ∀ n N : ℕ, cutoff c j n ≤ N →
      v - tailPartial k r c j N ∈ filtration k n ∧
      horizontal k r c j * v - normalizedPartial k r c j N ∈ filtration k n := by
    refine ⟨hv_unit, ?_⟩
    intro n N hN
    have hN' : c * (j + 1) < N := by
      dsimp [cutoff] at hN
      omega
    refine ⟨hv_tail n N hN, ?_⟩
    rw [normalizedPartial_eq_horizontal_mul_tail k r c j N hr hc0 hN']
    rw [← mul_sub]
    exact (filtration k n).mul_mem_left _ (hv_tail n N hN)
  refine ⟨v, hv_main, ?_⟩
  intro w hw
  letI : IsAdicComplete
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (by simp))
  have hcomp : IsAdicComplete
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := by
    exact (IsAdicComplete.map_algebraMap_iff
      (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1) (Chart k)).mpr inferInstance
  letI : IsHausdorff
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) (Chart k) := hcomp.1
  have hpow (n : ℕ) : filtration k n =
      ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
        (algebraMap (Node k) (Chart k))) ^ n := by
    simp [filtration, ArithmeticThetaScaledTateBridgeR0046.completedPower,
      ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
      ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.toCompleted, Ideal.map_span]
  apply (IsHausdorff.eq_iff_smodEq
    (I := (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1).map
      (algebraMap (Node k) (Chart k))) (M := Chart k)).mpr
  intro n
  rw [SModEq.sub_mem]
  let N := cutoff c j n
  have hv' := hv_tail n N (le_refl _)
  have hw' := (hw.2 n N (le_refl _)).1
  have hdiff : v - w ∈ filtration k n := by
    have htmp := (filtration k n).sub_mem hv' hw'
    convert htmp using 1 <;> ring
  have hdiff' := (filtration k n).neg_mem hdiff
  simpa [hpow, smul_eq_mul, Ideal.mul_top, sub_eq_add_neg] using hdiff'

end ArithmeticThetaAnnularTorsionPrereqR0053
