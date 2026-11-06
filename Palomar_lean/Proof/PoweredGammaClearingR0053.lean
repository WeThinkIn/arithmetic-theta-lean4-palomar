module

public import AnnularTorsionPrerequisiteDefinitionsR0053
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true

/-! Finite negative-exponent clearing for the powered local gamma product. -/
set_option autoImplicit false
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

open ArithmeticThetaScaledTateBridgeR0046

private lemma generic_xy (k : Type u) [Field k] [CharZero k] :
    toGeneric k (cx k) * toGeneric k (cy k) = toGeneric k (tau k) := by
  rw [← map_mul]
  change toGeneric k (ArithmeticThetaScaledAnnularR0050.cx k 1 *
    ArithmeticThetaScaledAnnularR0050.cy k 1) = _
  change toGeneric k (toCompleted k 1 (x k 1) * toCompleted k 1 (y k 1)) = _
  rw [← map_mul]
  congr 1
  change toCompleted k 1 (x k 1 * y k 1) = _
  have hrel : quotientMap k 1 (relation k 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxy : x k 1 * y k 1 = t k 1 := by
    apply sub_eq_zero.mp
    change quotientMap k 1 (MvPolynomial.X 0) * quotientMap k 1 (MvPolynomial.X 1) -
      algebraMap (Base k) (ArithmeticThetaScaledTateBridgeR0046.Node k 1)
        (parameter k 1) = 0
    change quotientMap k 1 (MvPolynomial.X 0) * quotientMap k 1 (MvPolynomial.X 1) -
      quotientMap k 1 (MvPolynomial.C (parameter k 1)) = 0
    simpa [relation, quotientMap] using hrel
  rw [hxy]
  simp [tau, ArithmeticThetaScaledAnnularR0050.tau, t, parameter,
    completedBaseMap]

private lemma tpower_one (k : Type u) [Field k] [CharZero k] :
    tpower k 1 = toGeneric k (tau k) := by
  change ((parameterUnit k) ^ (1 : ℤ)).val = _
  rw [zpow_one]
  exact (parameterUnit k).isUnit.unit_spec

private lemma tpower_add (k : Type u) [Field k] [CharZero k] (a b : ℤ) :
    tpower k (a + b) = tpower k a * tpower k b := by
  simp [tpower, zpow_add]

private lemma tpower_nat (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    tpower k (n : ℤ) = toGeneric k (tau k) ^ n := by
  induction n with
  | zero => simp [tpower]
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, tpower_add, ih,
        tpower_one]
      simp [pow_succ]

private lemma tpower_isUnit (k : Type u) [Field k] [CharZero k] (e : ℤ) :
    IsUnit (tpower k e) := by
  exact ((parameterUnit k) ^ e).isUnit

private lemma generic_y_isUnit (k : Type u) [Field k] [CharZero k] :
    IsUnit (toGeneric k (cy k)) := by
  apply isUnit_of_mul_isUnit_right
  rw [generic_xy]
  simpa [← tpower_one] using tpower_isUnit k 1

private lemma negative_factor_clear (k : Type u) [Field k] [CharZero k]
    (c : ℕ) (e : ℤ) (_he : e < 0) (hbound : e ≤ -(c : ℤ)) :
    1 - tpower k e * toGeneric k (cy k) ^ c =
      -(tpower k e * toGeneric k (cy k) ^ c) *
        (1 - toGeneric k (tau k) ^ (-e - (c : ℤ)).toNat * toGeneric k (cx k) ^ c) := by
  have hnonneg : 0 ≤ -e - (c : ℤ) := by omega
  have hsum : e + (-e - (c : ℤ)) + (c : ℤ) = 0 := by ring
  have hprod : (tpower k e * toGeneric k (cy k) ^ c) *
      (toGeneric k (tau k) ^ (-e - (c : ℤ)).toNat * toGeneric k (cx k) ^ c) = 1 := by
    rw [← tpower_nat k (-e - (c : ℤ)).toNat,
      show ((-e - (c : ℤ)).toNat : ℤ) = -e - (c : ℤ) by
        exact Int.toNat_of_nonneg hnonneg]
    have hpow : toGeneric k (cy k) ^ c * toGeneric k (cx k) ^ c =
        toGeneric k (tau k) ^ c := by
      rw [← mul_pow, mul_comm, generic_xy]
    calc
      (tpower k e * toGeneric k (cy k) ^ c) *
          (tpower k (-e - (c : ℤ)) * toGeneric k (cx k) ^ c) =
          (tpower k e * tpower k (-e - (c : ℤ))) *
            (toGeneric k (cy k) ^ c * toGeneric k (cx k) ^ c) := by ring
      _ = tpower k (e + (-e - (c : ℤ))) * toGeneric k (tau k) ^ c := by
        rw [← tpower_add, hpow]
      _ = tpower k (e + (-e - (c : ℤ))) * tpower k (c : ℤ) := by
        rw [tpower_nat]
      _ = tpower k (e + (-e - (c : ℤ)) + (c : ℤ)) := by
        rw [← tpower_add]
      _ = 1 := by rw [hsum]; simp [tpower]
  calc
    1 - tpower k e * toGeneric k (cy k) ^ c =
        -(tpower k e * toGeneric k (cy k) ^ c) + 1 := by ring
    _ = -(tpower k e * toGeneric k (cy k) ^ c) *
        (1 - toGeneric k (tau k) ^ (-e - (c : ℤ)).toNat * toGeneric k (cx k) ^ c) := by
      calc
        -(tpower k e * toGeneric k (cy k) ^ c) + 1 =
            -(tpower k e * toGeneric k (cy k) ^ c) +
              (tpower k e * toGeneric k (cy k) ^ c) *
                (toGeneric k (tau k) ^ (-e - (c : ℤ)).toNat * toGeneric k (cx k) ^ c) := by
              rw [hprod]
        _ = _ := by ring

private lemma factor_clearing (k : Type u) [Field k] [CharZero k]
    (r c j l : ℕ) (hneg : rightExponent r c j l < 0) (hbound : rightExponent r c j l ≤ -(c : ℤ)) :
    (1 - tpower k (leftExponent r c j l : ℤ) * toGeneric k (cx k) ^ c) *
      (1 - tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c) =
      (-(tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c)) *
        toGeneric k (normalizedFactor k r c j l) := by
  rw [negative_factor_clear k c _ hneg hbound]
  have hmap : toGeneric k (normalizedFactor k r c j l) =
      (1 - tpower k (leftExponent r c j l : ℤ) * toGeneric k (cx k) ^ c) *
        (1 - toGeneric k (tau k) ^
          (-rightExponent r c j l - (c : ℤ)).toNat * toGeneric k (cx k) ^ c) := by
    simp only [normalizedFactor, normalizedRight, map_mul, map_sub, map_one, map_pow]
    rw [if_pos hneg]
    rw [tpower_nat]
    simp
  rw [hmap]
  ring

private lemma tpower_nonneg (k : Type u) [Field k] [CharZero k]
    (e : ℤ) (he : 0 ≤ e) :
    tpower k e = toGeneric k (tau k) ^ e.toNat := by
  rw [← tpower_nat k e.toNat, Int.toNat_of_nonneg he]

theorem powered_gamma_clearing :
    ∀ (k : Type u) [Field k] [CharZero k] (r c j : ℕ),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 → j < r →
      (∀ l : ℕ, rightExponent r c j l < 0 → rightExponent r c j l ≤ -(c : ℤ)) ∧
      (∀ N : ℕ, literalPartial k r c j N =
        clearingPartial k r c j N * toGeneric k (normalizedPartial k r c j N) ∧
        IsUnit (clearingPartial k r c j N)) ∧
      (∀ M N : ℕ, cutoff c j 0 ≤ M → cutoff c j 0 ≤ N →
        clearingPartial k r c j M = clearingPartial k r c j N) := by
  intro k _ _ r c j hr hc hcr hcop hj
  have hbound : ∀ l : ℕ, rightExponent r c j l < 0 →
      rightExponent r c j l ≤ -(c : ℤ) := by
    intro l hneg
    rcases hcr with ⟨q, hq⟩
    have heq : rightExponent r c j l = (c : ℤ) *
        ((q : ℤ) * ((l : ℤ) + 1) - ((j : ℤ) + 1)) := by
      simp [rightExponent, hq]
      ring
    rw [heq] at hneg ⊢
    have hcZ : (0 : ℤ) < c := by
      exact_mod_cast (Nat.zero_lt_of_lt hc)
    have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hqzero
      simp [hqzero] at hq
      omega
    rcases Int.mul_neg_iff.mp hneg with hz | hz
    · have hzle : (q : ℤ) * ((l : ℤ) + 1) - ((j : ℤ) + 1) ≤ -1 := by omega
      have hcneg : (c : ℤ) * (-1) = -(c : ℤ) := by ring
      rw [← hcneg]
      exact (Int.mul_le_mul_left (by omega : (0 : ℤ) < c)).mpr hzle
    · exact False.elim (by omega)
  refine ⟨hbound, ?_, ?_⟩
  · intro N
    constructor
    · simp only [literalPartial, clearingPartial, normalizedPartial, map_prod]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro l hl
      by_cases hneg : rightExponent r c j l < 0
      · rw [if_pos hneg]
        exact factor_clearing k r c j l hneg (hbound l hneg)
      · rw [if_neg hneg]
        have hnonneg : 0 ≤ rightExponent r c j l := by omega
        have hmap : toGeneric k (normalizedFactor k r c j l) =
            (1 - tpower k (leftExponent r c j l : ℤ) * toGeneric k (cx k) ^ c) *
              (1 - tpower k (rightExponent r c j l) * toGeneric k (cy k) ^ c) := by
          simp only [normalizedFactor, normalizedRight, map_mul, map_sub, map_one, map_pow]
          rw [if_neg hneg, tpower_nat, tpower_nonneg k _ hnonneg]
          congr 1
          simp
        rw [hmap]
        ring
    · induction N with
      | zero => simp [clearingPartial]
      | succ N ih =>
          rw [clearingPartial, Finset.prod_range_succ]
          exact ih.mul (by
            split_ifs with hneg
            · exact ((tpower_isUnit k _).mul ((generic_y_isUnit k).pow c)).neg
            · exact isUnit_one)
  · have hcrle : c ≤ r := Nat.le_of_dvd hr hcr
    let K := cutoff c j 0
    have htail (l : ℕ) (hl : K ≤ l) : ¬ rightExponent r c j l < 0 := by
      simp only [K, cutoff] at hl
      have hcpos : 0 < c := by omega
      have hsmall : j + 1 ≤ c * (j + 1) := Nat.le_mul_of_pos_left _ hcpos
      have hjl : j + 1 ≤ l + 1 := by omega
      have hleft : c * (j + 1) ≤ c * (l + 1) :=
        Nat.mul_le_mul_left c hjl
      have hright : c * (l + 1) ≤ r * (l + 1) :=
        Nat.mul_le_mul_right (l + 1) hcrle
      have hsub : c * (j + 1) ≤ r * (l + 1) := hleft.trans hright
      have hsubZ : (c * (j + 1) : ℤ) ≤ r * (l + 1) := by
        exact_mod_cast hsub
      simp only [rightExponent]
      omega
    have hstable : ∀ q : ℕ, clearingPartial k r c j (K + q) =
        clearingPartial k r c j K := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
          rw [Nat.add_succ, clearingPartial, Finset.prod_range_succ]
          change clearingPartial k r c j (K + q) * _ = clearingPartial k r c j K
          rw [ih]
          simp [htail (K + q) (Nat.le_add_right K q)]
    intro M N hKM hKN
    rw [show M = K + (M - K) by omega, show N = K + (N - K) by omega,
      hstable, hstable]

end ArithmeticThetaAnnularTorsionPrereqR0053
