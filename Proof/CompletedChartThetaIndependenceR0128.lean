module

public import AnnularFullSeriesIdentificationR0128
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Rat.Star

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Independence in the actual completed node, detected by all unit
specializations and Dedekind independence of Laurent characters. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaAnnularThetaR0128
open ArithmeticThetaScaledAnnularR0050 ArithmeticThetaSchrodingerR0119

private def unitCharacter (k : Type u) [Field k] (b : ℤ) : kˣ →* k where
  toFun a := (a : k) ^ b
  map_one' := by simp
  map_mul' a c := by simp [mul_zpow]

private lemma unitCharacter_injective (k : Type u) [Field k] [CharZero k] :
    Function.Injective (unitCharacter k) := by
  intro b c h
  have hv := DFunLike.congr_fun h (Units.mk0 (2 : k) (by norm_num))
  change (2 : k) ^ b = (2 : k) ^ c at hv
  have hq : (2 : ℚ) ^ b = (2 : ℚ) ^ c := by
    apply Rat.cast_injective (α := k)
    simpa using hv
  exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) hq

private lemma laurent_characters_independent (k : Type u) [Field k] [CharZero k] :
    LinearIndependent k (fun b : ℤ => fun a : kˣ => (a : k) ^ b) :=
  (linearIndependent_monoidHom kˣ k).comp (unitCharacter k) (unitCharacter_injective k)

private lemma theta_specialization (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (he : Even m) (j : ℕ) (ν : Fin m) (a : kˣ) :
    specialize k a (thetaSection k m (NeZero.pos m) he j ν) =
      specializedSeries k 1 0 m 1 j (ν.val : ℤ) (a : k) := by
  have hchosen := Classical.choose_spec
    (theta_completed_limit k 1 m 1 j (ν.val : ℤ) (by decide)
      (NeZero.pos m) he (by decide))
  obtain ⟨s, hs, _⟩ := theta_limit_exact_specialization k 1 0 m 1 j (ν.val : ℤ)
    (by decide) (by decide) (NeZero.pos m) he (by decide) (a : k) a.ne_zero
  have hsame := hchosen.2 s hs.1
  simpa only [specialize, thetaSection, hsame] using hs.2

/-- Explicit adoption of the full-series predecessor for arbitrary coefficient
vectors, using the actual base map. -/
lemma combine_full_series (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (he : Even m) (j : ℕ)
    (w : Fin m → PowerSeries k) (a : kˣ) :
    (HahnSeries.ofPowerSeries ℤ k) (specialize k a (combine k m (NeZero.pos m) he j w)) =
      ∑ ν : Fin m, (HahnSeries.ofPowerSeries ℤ k) (w ν) *
        (monomial k (shift j : ℤ) * evaluate k (theta k m ν) (j : ℤ) a) := by
  classical
  simp only [combine, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [annular_full_series_identification]
  congr 1
  exact congrArg (HahnSeries.ofPowerSeries ℤ k)
    (specialization_base k 1 0 (by decide) (by decide) (a : k) a.ne_zero (w ν))

private lemma coeff_mul_stable (k : Type u) [Field k]
    (w f g : PowerSeries k) (n : ℕ)
    (h : ∀ d ≤ n, PowerSeries.coeff d f = PowerSeries.coeff d g) :
    PowerSeries.coeff n (w * f) = PowerSeries.coeff n (w * g) := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = n := by simpa using hp
  rw [h p.2 (by omega)]

private def weight (k : Type u) [Field k] (m j n : ℕ)
    (w : Fin m → PowerSeries k) (b : ℤ) : k :=
  ∑ ν : Fin m,
    if b % (m : ℤ) = (ν.val : ℤ) % (m : ℤ) then
      if (specializedExponent 1 0 1 j b).toNat ≤ n then
        PowerSeries.coeff (n - (specializedExponent 1 0 1 j b).toNat) (w ν)
      else 0
    else 0

private lemma finite_coefficient (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (he : Even m) (j n N : ℕ)
    (hN : n + 2 * (j+1) + 1 ≤ N) (w : Fin m → PowerSeries k) (a : kˣ) :
    PowerSeries.coeff n (∑ ν : Fin m,
      w ν * specializedSeries k 1 0 m 1 j (ν.val : ℤ) (a : k)) =
      ∑ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), weight k m j n w b * (a : k) ^ b := by
  classical
  simp only [map_sum]
  calc
    _ = ∑ ν : Fin m, PowerSeries.coeff n
        (w ν * specializedPartial k 1 0 m 1 j (ν.val : ℤ) (a : k) N) := by
      apply Finset.sum_congr rfl
      intro ν _
      apply coeff_mul_stable
      intro d hd
      exact ((specialized_coefficient_stability k 1 0 m 1 j (ν.val : ℤ)
        (a : k) (by decide) (by decide) (NeZero.pos m) he (by decide) a.ne_zero).2
        d N (by omega)).symm
    _ = _ := by
      simp only [specializedPartial, Finset.mul_sum, map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [weight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ν _
      split_ifs with hr hn
      · simp only [specializedTerm, ← mul_assoc, PowerSeries.coeff_mul_X_pow',
          if_pos hn, PowerSeries.coeff_mul_C]
      · simp only [specializedTerm, ← mul_assoc, PowerSeries.coeff_mul_X_pow',
          if_neg hn, zero_mul]
      · simp

private lemma weight_at_residue (k : Type u) [Field k] (m j n : ℕ)
    (w : Fin m → PowerSeries k) (ν : Fin m) :
    weight k m j (n + (specializedExponent 1 0 1 j (ν.val : ℤ)).toNat) w
      (ν.val : ℤ) = PowerSeries.coeff n (w ν) := by
  classical
  have hr (μ : Fin m) :
      (ν.val : ℤ) % (m : ℤ) = (μ.val : ℤ) % (m : ℤ) ↔ μ = ν := by
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast ν.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast μ.isLt)]
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      rfl
  simp [weight, hr]

private lemma weights_vanish (k : Type u) [Field k] [CharZero k]
    (m : ℕ) [NeZero m] (he : Even m) (j : ℕ) (w : Fin m → PowerSeries k)
    (h : ∀ a : kˣ, (∑ ν : Fin m,
      w ν * specializedSeries k 1 0 m 1 j (ν.val : ℤ) (a : k)) = 0)
    (n N : ℕ) (hN : n + 2 * (j+1) + 1 ≤ N) :
    ∀ b ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), weight k m j n w b = 0 := by
  classical
  apply (linearIndependent_iff'.mp (laurent_characters_independent k))
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← finite_coefficient k m he j n N hN w a, h a, map_zero]

/-- The coefficient vector is recovered from all scalar specializations of the
actual completed-node element; no individual specialization is asserted injective. -/
theorem completed_chart_theta_independence :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (he : Even m),
    ∀ j : ℕ, Function.Injective (combine k m (NeZero.pos m) he j) := by
  intro k _ _ m _ he j w w' h
  classical
  have hs (a : kˣ) : (∑ ν : Fin m,
      (w ν - w' ν) * specializedSeries k 1 0 m 1 j (ν.val : ℤ) (a : k)) = 0 := by
    have hf := (combine_full_series k m he j w a).symm.trans
      ((congrArg (fun s => (HahnSeries.ofPowerSeries ℤ k) (specialize k a s)) h).trans
        (combine_full_series k m he j w' a))
    simp_rw [← annular_full_series_identification k m he j, theta_specialization,
      ← map_mul] at hf
    rw [← map_sum, ← map_sum] at hf
    have hsum := HahnSeries.ofPowerSeries_injective hf
    simpa only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using hsum
  funext ν
  apply PowerSeries.ext
  intro n
  let d := (specializedExponent 1 0 1 j (ν.val : ℤ)).toNat
  have hz := weights_vanish k m he j (fun μ => w μ - w' μ) hs
    (n+d) (n+d+2*(j+1)+1+ν.val) (by omega) (ν.val : ℤ)
    (by simp only [Finset.mem_Icc]; constructor <;> omega)
  rw [weight_at_residue] at hz
  simpa only [map_sub, sub_eq_zero] using hz

end ArithmeticThetaAnnularThetaR0128
