module

public import ThetaLimitRecoveryRootR0128
public import AnnularThetaGluingDefinitionsR0128
public import ThetaAnnularConvergenceR0119
public import ScaledThetaLimitExactSpecializationR0050
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Data.Nat.Cast.SetInterval

@[expose] public section

/-! Identification of the actual completed-node theta limit with its full
Laurent-series evaluation, with the exact chart-dependent clearing factor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128
open ArithmeticThetaScaledAnnularR0050 ArithmeticThetaSchrodingerR0119

private lemma exponent_nonneg (j : ℕ) (b : ℤ) :
    0 ≤ specializedExponent 1 0 1 j b := by
  simp only [specializedExponent, thetaShift, Nat.add_zero, Nat.cast_add,
    Nat.cast_pow, Nat.cast_one, one_mul]
  nlinarith [sq_nonneg (b + (j : ℤ)), sq_nonneg b, sq_nonneg ((j : ℤ) + 1)]

private lemma exponent_gt_outside (j n : ℕ) (b : ℤ)
    (hb : b ∉ Finset.Icc (-((n + 2*(j+1)+1 : ℕ) : ℤ)) (n + 2*(j+1)+1)) :
    (n : ℤ) < specializedExponent 1 0 1 j b := by
  simp only [Finset.mem_Icc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, not_and_or, not_le] at hb
  simp only [specializedExponent, thetaShift, Nat.add_zero, Nat.cast_add,
    Nat.cast_pow, Nat.cast_one, one_mul]
  rcases hb with hb | hb
  · have h := mul_nonneg (show 0 ≤ -b - (j : ℤ) - 1 by omega)
      (show 0 ≤ -b by omega)
    nlinarith [sq_nonneg ((j : ℤ) + 1)]
  · have h := mul_nonneg (show 0 ≤ b - 1 by omega) (show 0 ≤ b by omega)
    have h' := mul_nonneg (show 0 ≤ (j : ℤ) by omega) (show 0 ≤ b by omega)
    nlinarith [sq_nonneg ((j : ℤ) + 1)]

private lemma specialized_term_laurent (k : Type u) [Field k]
    (m j : ℕ) (ν : Fin m) (a : kˣ) (b : ℤ) :
    (HahnSeries.ofPowerSeries ℤ k)
      (if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then
        specializedTerm k 1 0 1 j (a : k) b else 0) =
    monomial k (shift j : ℤ) * annularTerms k (theta k m ν) (j : ℤ) a b := by
  classical
  rw [theta_annular_term]
  change _ = monomial k (shift j : ℤ) *
    (if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then _ else _)
  split_ifs with h
  · simp only [specializedTerm, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, monomial,
      HahnSeries.single_mul_single, zero_add, mul_one, one_mul,
      Int.toNat_of_nonneg (exponent_nonneg j b)]
    congr 1
    simp [specializedExponent, shift, add_assoc]
  · simp

private lemma shifted_coefficient_partial (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (he : Even m) (j : ℕ) (ν : Fin m) (a : kˣ) (z : ℤ) :
    (monomial k (shift j : ℤ) * evaluate k (theta k m ν) (j : ℤ) a).coeff z =
    ((HahnSeries.ofPowerSeries ℤ k)
      (specializedPartial k 1 0 m 1 j (ν.val : ℤ) (a : k)
        (z.toNat + 2*(j+1)+1))).coeff z := by
  classical
  let : UniformSpace k := ⊥
  let T : ℤ → K k := fun b =>
    monomial k (shift j : ℤ) * annularTerms k (theta k m ν) (j : ℤ) a b
  have hs : HasSum T (monomial k (shift j : ℤ) *
      evaluate k (theta k m ν) (j : ℤ) a) :=
    ((theta_annular_convergence k m he ν (j : ℤ) a).2.hasSum).mul_left _
  have hc := hs.map (HahnSeries.coeff.addMonoidHom z)
    (LaurentSeries.uniformContinuous_coeff z).continuous
  have hz : ∀ b ∉ Finset.Icc (-((z.toNat+2*(j+1)+1 : ℕ) : ℤ))
      (z.toNat+2*(j+1)+1), (T b).coeff z = 0 := by
    intro b hb
    have hbound := exponent_gt_outside j z.toNat b hb
    have hne : z ≠ specializedExponent 1 0 1 j b := by omega
    dsimp [T]
    rw [← specialized_term_laurent]
    split_ifs
    · simp only [specializedTerm, map_mul, HahnSeries.ofPowerSeries_C,
        HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply,
        HahnSeries.single_mul_single, zero_add, mul_one,
        Int.toNat_of_nonneg (exponent_nonneg j b), HahnSeries.coeff_single, if_neg hne]
    · simp
  have heq := hc.unique (hasSum_sum_of_ne_finset_zero hz)
  change (monomial k (shift j : ℤ) * evaluate k (theta k m ν) (j : ℤ) a).coeff z =
    ∑ b ∈ Finset.Icc (-((z.toNat+2*(j+1)+1 : ℕ) : ℤ))
    (z.toNat+2*(j+1)+1), (T b).coeff z at heq
  rw [heq]
  unfold specializedPartial
  simp only [map_sum, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun f : K k => f.coeff z) (specialized_term_laurent k m j ν a b).symm

/-- The full bilateral series, with the exact clearing monomial on every chart. -/
theorem annular_full_series_identification :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (he : Even m),
    ∀ (j : ℕ) (ν : Fin m) (a : kˣ),
    (HahnSeries.ofPowerSeries ℤ k) (specialize k a
      (thetaSection k m (NeZero.pos m) he j ν)) =
    monomial k (shift j : ℤ) * evaluate k (theta k m ν) (j : ℤ) a := by
  intro k _ _ m _ he j ν a
  have hchosen := Classical.choose_spec
    (theta_completed_limit k 1 m 1 j (ν.val : ℤ) (by decide)
      (NeZero.pos m) he (by decide))
  obtain ⟨s, hs, _⟩ := theta_limit_exact_specialization k 1 0 m 1 j (ν.val : ℤ)
    (by decide) (by decide) (NeZero.pos m) he (by decide) (a : k) a.ne_zero
  have hspec : specialize k a (thetaSection k m (NeZero.pos m) he j ν) =
      specializedSeries k 1 0 m 1 j (ν.val : ℤ) (a : k) := by
    have hsame := hchosen.2 s hs.1
    simpa only [specialize, thetaSection, hsame] using hs.2
  rw [hspec]
  apply HahnSeries.ext
  funext z
  rw [shifted_coefficient_partial k m he j ν a z]
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff,
      specializedSeries, PowerSeries.coeff_mk]
  | negSucc n =>
    have hzero : ∀ f : PowerSeries k,
        ((HahnSeries.ofPowerSeries ℤ k) f).coeff (Int.negSucc n) = 0 := by
      intro f
      apply HahnSeries.embDomain_of_notMem_range
      simp
    rw [hzero, hzero]

end ArithmeticThetaAnnularThetaR0128
